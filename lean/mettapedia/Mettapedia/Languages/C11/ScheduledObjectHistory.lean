import Mettapedia.Languages.C11.ScheduledObjects

/-!
# Exact scheduled object histories and occurrence conservation

Every finite driver prefix constructs a connected history of the independent
scheduled memory transitions, ending at its complete saved state. This
includes exhaustion, selection suspension, success and refusal. A history
cannot splice another memory endpoint between receipts.

From unique initial occurrence identities, the whole history emits each
identity at most once. Its remaining occurrence count plus receipt count is
exactly the initial count. These are general laws for arbitrary admitted
finite operation plans, not only the concrete two-operation controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ScheduledObjectHistory

open ScheduledObjects
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Index Object Byte : Type}

inductive History (profile : ArrayPointers.DifferenceProfile) (plan : Plan Index Object Byte) :
    State Index Byte → List (Receipt Index Byte) → State Index Byte → Prop where
  | nil (state : State Index Byte) : History profile plan state [] state
  | cons (receipt : Receipt Index Byte) (events : List (Receipt Index Byte)) (final : State Index Byte)
      (justified : ValidReceipt profile plan receipt)
      (following : History profile plan receipt.after events final) :
      History profile plan receipt.before (receipt :: events) final

theorem History.origins {profile : ArrayPointers.DifferenceProfile} {plan : Plan Index Object Byte}
    {before after : State Index Byte} {events : List (Receipt Index Byte)}
    (history : History profile plan before events after) : ∀ receipt ∈ events, receipt.index ∈ before.pending := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ valid clean scheduled operation =>
          cases scheduled with
          | consume _ _ ready removed =>
              intro emitted present
              rcases List.mem_cons.mp present with rfl | present
              · exact ready.1
              · exact removed.sublist.subset (ih emitted present)

theorem History.account {profile : ArrayPointers.DifferenceProfile} {plan : Plan Index Object Byte}
    {before after : State Index Byte} {events : List (Receipt Index Byte)}
    (history : History profile plan before events after) :
    after.pending.length + events.length = before.pending.length := by
  induction history with
  | nil state => simp
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ valid clean scheduled operation =>
          cases scheduled with
          | consume _ _ ready removed =>
              have consumed := removed.length
              change receipt.after.pending.length + 1 = receipt.before.pending.length at consumed
              simp only [List.length_cons]
              omega

theorem History.unique {profile : ArrayPointers.DifferenceProfile} {plan : Plan Index Object Byte}
    {before after : State Index Byte} {events : List (Receipt Index Byte)}
    (history : History profile plan before events after) (unique : before.pending.Nodup) :
    (events.map (fun receipt => receipt.index)).Nodup ∧ after.pending.Nodup := by
  induction history with
  | nil state => exact ⟨by simp, unique⟩
  | cons receipt events final justified following ih =>
      cases justified with
      | execute _ _ _ valid clean scheduled operation =>
          cases scheduled with
          | consume _ _ ready removed =>
              obtain ⟨laterUnique, residualUnique⟩ := ih (removed.unique unique)
              refine ⟨?_, residualUnique⟩
              simp only [List.map_cons, List.nodup_cons]
              refine ⟨?_, laterUnique⟩
              intro repeated
              obtain ⟨later, present, same⟩ := List.mem_map.mp repeated
              have pending := following.origins later present
              rw [same] at pending
              exact removed.absent unique pending

def endpoint : Outcome (Configuration Index Byte) (Verdict Index Byte) (SelectionRequest Index) →
    Option (State Index Byte)
  | .exhausted saved | .stuck saved | .suspended _ saved => some saved.state
  | .finished (.returned saved) | .finished (.refused saved) => some saved.state
  | .faulted => none

theorem run_history [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (fuel : Nat) (initial : Configuration Index Byte) :
    ∃ final, endpoint ((machine profile plan).run fuel initial).2 = some final ∧
      History profile plan initial.state ((machine profile plan).run fuel initial).1 final := by
  induction fuel generalizing initial with
  | zero => exact ⟨initial.state, rfl, .nil _⟩
  | succ fuel ih =>
      by_cases allowed : admissible plan = true
      · cases pending : initial.state.pending with
        | nil =>
            have ran : (machine profile plan).run (fuel + 1) initial = ([], .finished (.returned initial)) := by
              simp [Machine.run, machine, allowed, pending]
            rw [ran]
            exact ⟨initial.state, rfl, .nil _⟩
        | cons head tail =>
            cases selections : initial.selections with
            | nil =>
                have ran : (machine profile plan).run (fuel + 1) initial =
                    ([], .suspended ⟨SequencingSchedule.choices plan.evaluation.order initial.state.pending⟩ initial) := by
                  simp [Machine.run, machine, allowed, pending, selections]
                rw [ran]
                exact ⟨initial.state, rfl, .nil _⟩
            | cons selection rest =>
                cases computed : execute profile plan selection.allocator initial.state selection.index with
                | none =>
                    have ran : (machine profile plan).run (fuel + 1) initial = ([], .finished (.refused initial)) := by
                      simp [Machine.run, machine, allowed, pending, selections, computed]
                    rw [ran]
                    exact ⟨initial.state, rfl, .nil _⟩
                | some result =>
                    rcases result with ⟨response, after⟩
                    let receipt : Receipt Index Byte := ⟨selection.index, response, initial.state, after⟩
                    have stepped : (machine profile plan).step initial = some (.publish [receipt] ⟨after, rest⟩) := by
                      simp [machine, allowed, pending, selections, computed, receipt]
                    rw [(machine profile plan).run_succ_publish stepped]
                    obtain ⟨final, endState, following⟩ := ih ⟨after, rest⟩
                    exact ⟨final, endState,
                      .cons receipt _ final
                        (execute_sound profile plan selection.allocator initial.state after selection.index response computed)
                        following⟩
      · have ran : (machine profile plan).run (fuel + 1) initial = ([], .finished (.refused initial)) := by
          simp [Machine.run, machine, allowed]
        rw [ran]
        exact ⟨initial.state, rfl, .nil _⟩

theorem run_conserves_occurrences [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (fuel : Nat) (initial : Configuration Index Byte) :
    ∃ final, endpoint ((machine profile plan).run fuel initial).2 = some final ∧
      final.pending.length + ((machine profile plan).run fuel initial).1.length = initial.state.pending.length := by
  obtain ⟨final, endState, history⟩ := run_history profile plan fuel initial
  exact ⟨final, endState, history.account⟩

theorem run_unique_occurrences [DecidableEq Index] [DecidableEq Object] (profile : ArrayPointers.DifferenceProfile)
    (plan : Plan Index Object Byte) (fuel : Nat) (initial : Configuration Index Byte)
    (unique : initial.state.pending.Nodup) :
    (((machine profile plan).run fuel initial).1.map (fun receipt => receipt.index)).Nodup := by
  obtain ⟨final, endState, history⟩ := run_history profile plan fuel initial
  exact (history.unique unique).1

end Mettapedia.Languages.C11.ScheduledObjectHistory
