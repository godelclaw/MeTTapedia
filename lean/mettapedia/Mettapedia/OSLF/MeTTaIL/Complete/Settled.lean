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
