import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Languages.MeTTa.HE.RecursiveTaskOrder
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Constructed administrative progress of first-success control

The order retains every pending continuation as a separate token. Expanding a
request replaces its token by smaller request/continuation tokens. Consuming a
continuation also decreases this order, including when an arbitrarily long
ordered reply is inserted. The multiset order is well founded independently of
any evaluator denotation. Its deterministic descent constructs a finite work
account and the common productive-machine instance.

This bounds administration in the existing fuel-indexed recursive profile.
It neither asserts termination of unbounded source programs nor supplies
native callback, effect or allocator correctness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveProgress

open RecursiveTasks FirstSuccessRecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Key := Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat

def key (fuel layer remaining phase : Nat) : Key :=
  toLex (fuel, toLex (layer, toLex (remaining, phase)))

def workKey (task : Task) : Key :=
  let parts := RecursiveTaskOrder.taskKey task
  key parts.1 parts.2.1 parts.2.2 2

def appendKey (task : Task) : Key :=
  let parts := RecursiveTaskOrder.taskKey task
  key parts.1 parts.2.1 parts.2.2 3

def frameKey : Frame → Key
  | .heads _ _ fuel _ | .argumentHeads _ _ _ fuel _ | .tupleHeads _ fuel _ => key fuel 4 0 0
  | .calls _ fuel _ | .invocationReturn _ _ fuel _ => key fuel 3 0 0
  | .producerResults _ _ _ fuel _ _ => key fuel 5 0 0
  | .minimalResults fuel _ _ | .chainResults _ _ fuel | .bodyResults fuel _ _ =>
      key fuel 2 0 0
  | .append task => appendKey task
  | _ => key 0 0 0 1

def controlKeys : Control → List Key
  | .work task => [workKey task]
  | .returning _ => []

def expansionKeys (expanded : Control × List Frame) : List Key :=
  controlKeys expanded.1 ++ expanded.2.map frameKey

attribute [local simp] expansionKeys controlKeys frameKey workKey appendKey key
  RecursiveTaskOrder.taskKey Prod.Lex.toLex_lt_toLex

set_option maxHeartbeats 800000 in
/-- Fuel, phase and remaining occurrences establish every request dependency,
without evaluating a denotation of a surrounding continuation. -/
theorem enter_smaller (space : Space) (dispatch : GroundedDispatch) (task : Task)
    {lookup : TypeLookup} (child : Key) (spawned : child ∈ expansionKeys
      (FirstSuccessRecursiveStrategy.enter space dispatch task lookup)) :
    child < workKey task := by
  cases task <;>
    simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] at spawned <;>
    repeat' split at spawned
  all_goals
    try simp_all
    repeat' rcases spawned with rfl | spawned
    all_goals try simp_all
    all_goals try omega

theorem resume_smaller (space : Space) (frame : Frame) (results : ResultSet)
    {lookup : TypeLookup} (child : Key)
    (spawned : child ∈ expansionKeys (RecursiveMachine.resume space frame results lookup)) :
    child < frameKey frame := by
  cases frame <;> simp only [RecursiveMachine.resume] at spawned <;>
    repeat' split at spawned
  all_goals
    try simp_all
    repeat' rcases spawned with rfl | spawned
    all_goals try simp_all
    all_goals try omega

def tokens (state : Configuration) : Multiset Key :=
  (controlKeys state.control ++ state.stack.map frameKey : List Key)

def Smaller (before after : Configuration) : Prop :=
  Multiset.IsDershowitzMannaLT (tokens before) (tokens after)

theorem smaller_wellFounded : WellFounded Smaller :=
  InvImage.wf tokens Multiset.wellFounded_isDershowitzMannaLT

theorem next_smaller (dispatch : GroundedDispatch) (state after : Configuration)
    {policy : TypePolicy} (advanced : next dispatch state policy = some after) :
    Smaller after state := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work task =>
          cases advanced
          let lookup := policy.types ⟨space, .work task, stack, emitted⟩
          refine ⟨(stack.map frameKey : Multiset Key),
            (expansionKeys (FirstSuccessRecursiveStrategy.enter space dispatch task lookup) :
              Multiset Key),
            {workKey task}, by simp, ?_, ?_, ?_⟩
          · change (↑(controlKeys (FirstSuccessRecursiveStrategy.enter space dispatch task lookup).1 ++
                ((FirstSuccessRecursiveStrategy.enter space dispatch task lookup).2 ++ stack).map
                  frameKey) :
                Multiset Key) = ↑(stack.map frameKey) +
              ↑(controlKeys (FirstSuccessRecursiveStrategy.enter space dispatch task lookup).1 ++
                (FirstSuccessRecursiveStrategy.enter space dispatch task lookup).2.map frameKey)
            rw [List.map_append, ← List.append_assoc, ← Multiset.coe_add]
            exact add_comm _ _
          · change (↑([workKey task] ++ stack.map frameKey) : Multiset Key) =
              ↑(stack.map frameKey) + {workKey task}
            rw [← Multiset.coe_add]
            exact add_comm _ _
          · intro child member
            exact ⟨workKey task, by simp, enter_smaller space dispatch task child member⟩
      | returning results =>
          cases stack with
          | nil => simp [next] at advanced
          | cons frame remaining =>
              cases advanced
              let lookup := policy.types ⟨space, .returning results, frame :: remaining, emitted⟩
              refine ⟨(remaining.map frameKey : Multiset Key),
                (expansionKeys (RecursiveMachine.resume space frame results lookup) : Multiset Key),
                {frameKey frame}, by simp, ?_, ?_, ?_⟩
              · change (↑(controlKeys (RecursiveMachine.resume space frame results lookup).1 ++
                    ((RecursiveMachine.resume space frame results lookup).2 ++ remaining).map
                      frameKey) :
                    Multiset Key) = ↑(remaining.map frameKey) +
                  ↑(controlKeys (RecursiveMachine.resume space frame results lookup).1 ++
                    (RecursiveMachine.resume space frame results lookup).2.map frameKey)
                rw [List.map_append, ← List.append_assoc, ← Multiset.coe_add]
                exact add_comm _ _
              · change (↑([frameKey frame] ++ remaining.map frameKey) : Multiset Key) =
                  ↑(remaining.map frameKey) + {frameKey frame}
                rw [← Multiset.coe_add]
                exact add_comm _ _
              · intro child member
                exact ⟨frameKey frame, by simp, resume_smaller space frame results child member⟩

/-- A finite bound is constructed by the machine's own well-founded descent;
no source-termination bound is an input. -/
def work (dispatch : GroundedDispatch) : Configuration → Nat :=
  smaller_wellFounded.fix fun state recur =>
    match found : next dispatch state with
    | none => 0
    | some after => recur after (next_smaller dispatch state after found) + 1

theorem work_unfold (dispatch : GroundedDispatch) (state : Configuration) :
    work dispatch state = match next dispatch state with
      | none => 0
      | some after => work dispatch after + 1 := by
  conv_lhs => rw [work, WellFounded.fix_eq]
  split <;> simp_all only [work]

theorem silent_decreases (dispatch : GroundedDispatch) (state after : Configuration)
    (advanced : (machine dispatch).step state = some (.silent after)) :
    work dispatch after < work dispatch state := by
  cases found : next dispatch state with
  | some successor =>
      have equal : successor = after := by simpa [machine, found] using advanced
      subst successor
      rw [work_unfold dispatch state, found]
      exact Nat.lt_succ_self _
  | none =>
      cases control : state.control with
      | work task => simp [machine, found, control] at advanced
      | returning results => cases results <;> simp [machine, found, control] at advanced

def productive (dispatch : GroundedDispatch) : (machine dispatch).Productive where
  rank := work dispatch
  silent_decreases := by intro state after advanced; exact silent_decreases dispatch state after advanced
  moves := by
    intro state
    obtain ⟨action, found⟩ := step_moves dispatch state
    rw [found]
    simp

theorem administrative_progress (dispatch : GroundedDispatch) (state : Configuration) :
    ∃ count ≤ work dispatch state, ∃ settled action,
      (machine dispatch).run count state = ([], .exhausted settled) ∧
      (machine dispatch).step settled = some action ∧ action.administrative = false :=
  (productive dispatch).settles state

end Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveProgress
