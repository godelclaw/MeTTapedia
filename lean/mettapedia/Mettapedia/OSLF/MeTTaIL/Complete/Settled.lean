import Mettapedia.OSLF.MeTTaIL.Complete.Explore
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-!
# Settled exploration

A search is *stable* when a complete run stays complete and publishes nothing more under further
work. An explorer is *settled* when every node's search is complete and every receipt it
published already has its child. A settled explorer's states never change again, so exploration
may stop there: `roundsUntilSettled` gives exactly the states of the full number of rounds.

The search modulo equations is stable: a complete state's lanes are certified and drained, a
tick leaves them unchanged (`Deep.tick_complete`), so a round only advances the round counter.
The same holds in standard form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Settled

open Mettapedia.Machines.ResumableSearchRunner (Search Status)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer expand step)

variable {σ Run Receipt : Type} [DecidableEq σ] (S : Search σ Run Receipt)

/-- Complete runs stay complete and publish nothing more. -/
def Stable : Prop :=
  ∀ run work, S.status run = .complete →
    S.publication (S.resume run work) = S.publication run ∧ S.status (S.resume run work) = .complete

/-- A node whose search is complete and whose receipts all have their children. -/
def nodeSettled (node : Node σ Run Receipt) : Bool :=
  S.status node.run == .complete && node.consumed == (S.publication node.run).length

/-- Every node is settled. -/
def settled (explorer : Explorer σ Run Receipt) : Bool := explorer.nodes.all (nodeSettled S)

variable {S}

omit [DecidableEq σ] in
theorem expand_settled (stable : Stable S) (round : Nat) (node : Node σ Run Receipt)
    (done : nodeSettled S node = true) :
    (expand S round node).2 = [] ∧ (expand S round node).1.state = node.state ∧
      nodeSettled S (expand S round node).1 = true := by
  simp only [nodeSettled, Bool.and_eq_true, beq_iff_eq] at done
  obtain ⟨complete, consumed⟩ := done
  obtain ⟨same, stays⟩ := stable node.run 1 complete
  refine ⟨?_, rfl, ?_⟩
  · show List.map _ ((S.publication (S.resume node.run 1)).drop node.consumed) = []
    rw [same, consumed, List.drop_length, List.map_nil]
  · show (S.status (S.resume node.run 1) == .complete &&
        (S.publication (S.resume node.run 1)).length == (S.publication (S.resume node.run 1)).length) = true
    simp [stays]

/-- **A settled explorer's step keeps its states and stays settled.** -/
theorem step_settled (stable : Stable S) (explorer : Explorer σ Run Receipt) (done : settled S explorer = true) :
    (step S explorer).nodes.map (·.state) = explorer.nodes.map (·.state) ∧ settled S (step S explorer) = true := by
  have each : ∀ node ∈ explorer.nodes, nodeSettled S node = true := List.all_eq_true.mp done
  have noChildren : (explorer.nodes.map (expand S explorer.round)).flatMap Prod.snd = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro pair member
    obtain ⟨node, inside, rfl⟩ := List.mem_map.mp member
    exact (expand_settled stable explorer.round node (each node inside)).1
  refine ⟨?_, ?_⟩
  · simp only [step, noChildren, Complete.Explore.fresh, List.append_nil, List.map_map]
    apply List.map_congr_left
    intro node inside
    exact (expand_settled stable explorer.round node (each node inside)).2.1
  · simp only [settled, step, noChildren, Complete.Explore.fresh, List.append_nil, List.all_map]
    apply List.all_eq_true.mpr
    intro node inside
    exact (expand_settled stable explorer.round node (each node inside)).2.2

theorem iterate_settled (stable : Stable S) : ∀ (work : Nat) (explorer : Explorer σ Run Receipt),
    settled S explorer = true →
      (Nat.iterate (step S) work explorer).nodes.map (·.state) = explorer.nodes.map (·.state) ∧
        settled S (Nat.iterate (step S) work explorer) = true
  | 0, _, done => ⟨rfl, done⟩
  | work + 1, explorer, done => by
    obtain ⟨same, still⟩ := step_settled stable explorer done
    obtain ⟨later, stays⟩ := iterate_settled stable work (step S explorer) still
    simp only [Function.iterate_succ_apply]
    exact ⟨later.trans same, stays⟩

variable (S)

/-- Up to `work` rounds, stopping as soon as the explorer is settled. -/
def roundsUntilSettled : Nat → Explorer σ Run Receipt → Explorer σ Run Receipt
  | 0, explorer => explorer
  | work + 1, explorer => if settled S explorer then explorer else roundsUntilSettled work (step S explorer)

variable {S}

/-- **Stopping when settled gives the states of every round.** -/
theorem roundsUntilSettled_states (stable : Stable S) : ∀ (work : Nat) (explorer : Explorer σ Run Receipt),
    (roundsUntilSettled S work explorer).nodes.map (·.state) =
      (Nat.iterate (step S) work explorer).nodes.map (·.state)
  | 0, _ => rfl
  | work + 1, explorer => by
    simp only [roundsUntilSettled]
    split
    · rename_i done
      exact (iterate_settled stable (work + 1) explorer done).1.symm
    · rw [Function.iterate_succ_apply]
      exact roundsUntilSettled_states stable work (step S explorer)

theorem roundsUntilSettled_of_settled (explorer : Explorer σ Run Receipt)
    (done : settled S explorer = true) (work : Nat) :
    roundsUntilSettled S work explorer = explorer := by
  cases work with
  | zero => rfl
  | succ work => simp [roundsUntilSettled, done]

theorem roundsUntilSettled_add (first extra : Nat) (explorer : Explorer σ Run Receipt) :
    roundsUntilSettled S (first + extra) explorer =
      roundsUntilSettled S extra (roundsUntilSettled S first explorer) := by
  induction first generalizing explorer with
  | zero => simp only [Nat.zero_add, roundsUntilSettled]
  | succ first ih =>
      by_cases done : settled S explorer = true
      · simp only [roundsUntilSettled_of_settled (S := S) explorer done]
      · simp only [Nat.succ_add, roundsUntilSettled, done]
        exact ih (step S explorer)

#print axioms roundsUntilSettled_of_settled
#print axioms roundsUntilSettled_add

/-! ## The search modulo equations is stable -/

section Classes

open GeneralExecutionAdmission
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

theorem advance_complete (entry : Classes.Entry plan) (done : entry.2.complete = true) :
    Classes.advance plan bound expected entry = (entry, []) := by
  obtain ⟨key, deep⟩ := entry
  simp only [Classes.advance, Deep.tick_complete _ done, List.drop_length]
  cases key <;> simp [Classes.events]

/-- **A round on a complete state only advances the round counter.** -/
theorem round_complete (state : Classes.State plan) (done : Classes.complete plan state = true) :
    Classes.round plan bound expected state = { state with round := state.round + 1 } := by
  have each : ∀ entry ∈ state.entries, entry.2.complete = true := List.all_eq_true.mp done
  have advanced : state.entries.map (Classes.advance plan bound expected) = state.entries.map (·, []) :=
    List.map_congr_left fun entry inside => advance_complete plan bound expected entry (each entry inside)
  obtain ⟨round, reps, entries, log⟩ := state
  have noEvents : entries.flatMap (fun _ => ([] : List Classes.Event)) = [] := by simp
  have kept : entries.map (Prod.fst ∘ fun entry => (entry, ([] : List Classes.Event))) = entries := by
    simp [Function.comp_def]
  simp only [Classes.round, advanced, List.flatMap_map, List.map_map]
  simp only [noEvents, kept]
  simp [Classes.addDiscoveries, Classes.firings]

theorem rounds_complete (state : Classes.State plan) (done : Classes.complete plan state = true) :
    ∀ work, Classes.rounds plan bound expected work state = { state with round := state.round + work }
  | 0 => rfl
  | work + 1 => by
    simp only [Classes.rounds, round_complete plan bound expected state done]
    rw [rounds_complete { state with round := state.round + 1 } done work]
    simp only [Nat.add_assoc, Nat.add_comm 1 work]

theorem classes_stable : Stable (Classes.search plan bound expected) := by
  intro run work complete
  have done : Classes.complete plan run = true := by
    simp only [Classes.search, Classes.status] at complete
    split at complete
    · assumption
    · cases complete
  simp only [Classes.search, rounds_complete plan bound expected run done work]
  refine ⟨trivial, ?_⟩
  have same : Classes.complete plan { run with round := run.round + work } = Classes.complete plan run := rfl
  simp only [Classes.status, same, done, if_true]

/-- **Normalized exploration may stop once settled.** -/
theorem normalized_stable (mode : Normalized.Commit := .standard) : Stable (Normalized.search plan bound expected mode) :=
  classes_stable plan bound expected

end Classes

end Mettapedia.OSLF.MeTTaIL.Complete.Settled


namespace Mettapedia.OSLF.MeTTaIL.Complete.Settled

open Mettapedia.Machines.ResumableSearchRunner (Search Status)
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer expand step explore Explored)

variable {σ Run Receipt : Type} [DecidableEq σ] {S : Search σ Run Receipt}

private theorem persist_more (source : σ) (work more : Nat)
    (node : Node σ Run Receipt) (present : node ∈ (explore S source work).nodes) :
    ∃ later ∈ (explore S source (work + more)).nodes,
      later.state = node.state ∧ later.born = node.born := by
  induction more with
  | zero => exact ⟨node, present, rfl, rfl⟩
  | succ more ih =>
      obtain ⟨later, inside, same, born⟩ := ih
      obtain ⟨next, nextInside, nextSame, nextBorn⟩ := Explore.nodes_persist source _ later inside
      exact ⟨next, by simpa only [Nat.add_assoc] using nextInside,
        nextSame.trans same, nextBorn.trans born⟩

private theorem fresh_unseen (seen : List σ) (children : List (Node σ Run Receipt))
    (node : Node σ Run Receipt) (present : node ∈ Explore.fresh seen children) : node.state ∉ seen := by
  induction children generalizing seen with
  | nil => cases present
  | cons child children ih =>
      simp only [Explore.fresh] at present
      split at present
      · exact ih seen present
      · rename_i unknown
        rcases List.mem_cons.mp present with rfl | remaining
        · exact unknown
        · intro known
          exact ih (child.state :: seen) remaining (List.mem_cons_of_mem _ known)

private theorem finite_discovery_cutoff (source : σ) (carrier : List σ) :
    ∃ cutoff, ∀ state ∈ carrier, Explored (S := S) source state →
      ∃ node ∈ (explore S source cutoff).nodes, node.state = state := by
  classical
  induction carrier with
  | nil => exact ⟨0, by intro state member; cases member⟩
  | cons state carrier ih =>
      obtain ⟨cutoff, covered⟩ := ih
      by_cases reached : Explored (S := S) source state
      · obtain ⟨round, node, present, same⟩ := reached
        refine ⟨round + cutoff, ?_⟩
        intro target member explored
        rcases List.mem_cons.mp member with rfl | inside
        · obtain ⟨later, laterInside, laterSame, _⟩ := persist_more source round cutoff node present
          exact ⟨later, laterInside, laterSame.trans same⟩
        · obtain ⟨old, oldInside, oldSame⟩ := covered target inside explored
          obtain ⟨later, laterInside, laterSame, _⟩ := persist_more source cutoff round old oldInside
          exact ⟨later, by simpa only [Nat.add_comm cutoff round] using laterInside,
            laterSame.trans oldSame⟩
      · refine ⟨cutoff, ?_⟩
        intro target member explored
        rcases List.mem_cons.mp member with rfl | inside
        · exact False.elim (reached explored)
        · exact covered target inside explored

omit [DecidableEq σ] in
private theorem complete_later (lawful : S.Lawful) (stable : Stable S)
    (source : σ) (first extra : Nat) (done : S.status (S.run source first) = .complete) :
    S.status (S.run source (first + extra)) = .complete := by
  rw [← lawful.resume_run]
  exact (stable _ extra done).2

omit [DecidableEq σ] in
private theorem uniform_local_finish (lawful : S.Lawful) (stable : Stable S)
    (carrier : List σ) (drains : ∀ state ∈ carrier, ∃ work, S.status (S.run state work) = .complete) :
    ∃ work, ∀ state ∈ carrier, S.status (S.run state work) = .complete := by
  induction carrier with
  | nil => exact ⟨0, by intro state member; cases member⟩
  | cons state carrier ih =>
      obtain ⟨first, done⟩ := drains state List.mem_cons_self
      obtain ⟨later, restDone⟩ := ih (fun target member => drains target (List.mem_cons_of_mem _ member))
      refine ⟨first + later, ?_⟩
      intro target member
      rcases List.mem_cons.mp member with rfl | inside
      · exact complete_later lawful stable target first later done
      · simpa only [Nat.add_comm later first] using
          complete_later lawful stable target later first (restDone target inside)

/-- A finite state carrier and genuine local drainage suffice for the actual
explorer to settle. Receipts to old states remain in their source runs. The
conclusion makes no claim about unfolded histories through graph cycles. -/
theorem eventually_settled_of_finite_carrier (lawful : S.Lawful) (stable : Stable S)
    (source : σ) (carrier : List σ)
    (within : ∀ work, ∀ node ∈ (explore S source work).nodes, node.state ∈ carrier)
    (drains : ∀ state ∈ carrier, ∃ work, S.status (S.run state work) = .complete) :
    ∃ work, settled S (explore S source work) = true := by
  obtain ⟨cutoff, covered⟩ := finite_discovery_cutoff (S := S) source carrier
  have allCovered : ∀ state, Explored (S := S) source state →
      ∃ node ∈ (explore S source cutoff).nodes, node.state = state := by
    intro state reached
    obtain ⟨work, node, present, same⟩ := reached
    exact covered state (same ▸ within work node present) ⟨work, node, present, same⟩
  have bornBound : ∀ extra, ∀ node ∈ (explore S source (cutoff + extra)).nodes, node.born ≤ cutoff := by
    intro extra
    induction extra with
    | zero =>
        intro node present
        simpa only [Nat.add_zero, Explore.explore_round] using
          (Explore.explore_good lawful source cutoff).born node present
    | succ extra ih =>
        intro node present
        change node ∈ (step S (explore S source (cutoff + extra))).nodes at present
        simp only [step, List.mem_append] at present
        rcases present with old | fresh
        · obtain ⟨pair, pairInside, rfl⟩ := List.mem_map.mp old
          obtain ⟨earlier, earlierInside, rfl⟩ := List.mem_map.mp pairInside
          exact ih earlier earlierInside
        · have inNext : node ∈ (explore S source (cutoff + extra + 1)).nodes := by
            exact List.mem_append_right _ fresh
          obtain ⟨early, earlyInside, earlySame⟩ := allCovered node.state ⟨_, node, inNext, rfl⟩
          obtain ⟨now, nowInside, nowSame, _⟩ := persist_more source cutoff extra early earlyInside
          have known : node.state ∈
              (((explore S source (cutoff + extra)).nodes.map (expand S (explore S source (cutoff + extra)).round)).map Prod.fst).map (·.state) := by
            refine List.mem_map.mpr ⟨(expand S (explore S source (cutoff + extra)).round now).1, ?_, ?_⟩
            · exact List.mem_map_of_mem (List.mem_map_of_mem nowInside)
            · exact nowSame.trans earlySame
          exact False.elim (fresh_unseen _ _ node fresh known)
  obtain ⟨budget, finished⟩ := uniform_local_finish lawful stable carrier drains
  refine ⟨cutoff + budget + 1, List.all_eq_true.mpr ?_⟩
  intro node present
  have good := Explore.explore_good lawful source (cutoff + budget + 1)
  have born : node.born ≤ cutoff := by
    apply bornBound (budget + 1) node
    simpa only [Nat.add_assoc] using present
  have enough : budget ≤ (explore S source (cutoff + budget + 1)).round - node.born := by
    rw [Explore.explore_round]
    omega
  obtain ⟨more, total⟩ := Nat.exists_eq_add_of_le enough
  have done := complete_later lawful stable node.state budget more (finished node.state (within _ node present))
  rw [← total, ← good.run node present] at done
  simp only [nodeSettled, Bool.and_eq_true, beq_iff_eq]
  refine ⟨done, good.expanded node present ?_⟩
  rw [Explore.explore_round]
  omega

omit [DecidableEq σ] in
private theorem history_head_within (carrier : List σ)
    (closed : ∀ state ∈ carrier, ∀ receipt, S.Valid state receipt → S.target receipt ∈ carrier)
    (source : σ) (initial : source ∈ carrier)
    {states : List σ} {receipts : List Receipt}
    (history : Mettapedia.Machines.ResumableSearchRunner.History S states receipts) :
    ∀ current, states.head? = some current → states.getLast? = some source → current ∈ carrier := by
  induction history with
  | start first =>
      intro current head last
      have same : first = current := by simpa only [List.head?_cons, Option.some.injEq] using head
      have origin : first = source := by simpa only [List.getLast?_singleton, Option.some.injEq] using last
      exact (same.symm.trans origin) ▸ initial
  | @commit state states receipts receipt history valid ih =>
      intro current head last
      have priorLast : (state :: states).getLast? = some source := by
        simpa only [List.getLast?_cons_cons] using last
      have known := ih state rfl priorLast
      have same : S.target receipt = current := by
        simpa only [List.head?_cons, Option.some.injEq] using head
      exact same ▸ closed state known receipt valid

/-- Closure under actual valid receipts supplies the finite carrier premise
of the explorer drainage theorem. No discovery-tree edge is discarded. -/
theorem eventually_settled_of_closed_carrier (lawful : S.Lawful) (stable : Stable S)
    (source : σ) (carrier : List σ) (initial : source ∈ carrier)
    (closed : ∀ state ∈ carrier, ∀ receipt, S.Valid state receipt → S.target receipt ∈ carrier)
    (drains : ∀ state ∈ carrier, ∃ work, S.status (S.run state work) = .complete) :
    ∃ work, settled S (explore S source work) = true := by
  apply eventually_settled_of_finite_carrier lawful stable source carrier _ drains
  intro work node present
  obtain ⟨history, head, last⟩ := Explore.node_chain lawful source work node present
  exact history_head_within carrier closed source initial history node.state head last

#print axioms eventually_settled_of_closed_carrier

#print axioms eventually_settled_of_finite_carrier

end Mettapedia.OSLF.MeTTaIL.Complete.Settled
