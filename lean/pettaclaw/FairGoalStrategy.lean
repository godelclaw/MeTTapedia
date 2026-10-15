import FairGoalScheduling

/-!

Historical/design model: this file records a policy studied before the sequential
tool simplification. Its holds, quotas, or scheduling assumptions are not the
current dispatch contract. See `SequentialTools.lean` for that contract and
`CommandHolds.lean` for the conditional costs of the removed hold policy.
# Fair service at the observed-strategy boundary

This adapter uses `GoalSystem.State` directly: no parallel goal database,
review-only queue or separate completion rule. One admitted provider attempt
costs one service unit, regardless of its later response. The host bounds
the work inside a turn separately; fairness of turns does not imply fairness
of tokens, time or arbitrarily large tool batches.

All provider capture events pass through the fair selector and the existing
active-request, input, observation, interruption, allowance and cooldown
checks. Charging and capture form one checkpoint transition. Replaying a
capture while it is pending cannot charge or submit it again. A restart
preserves spent service even when it drops a volatile provider request.

Completion still uses the existing observed receipt and task checker. The
host must persist the whole state atomically and use unique stable goal IDs.
Fresh goal admission and changes to shares are separate configuration
operations; the finite-cohort bound does not cover unlimited reconfiguration.
-/

namespace FairGoalStrategy

open GoalSystem
open Mettapedia.CogArch.Agent

def next (state : State) (admitted : Bool) : Choice :=
  if !state.agent.requests.inbox.isEmpty then .input
  else if !admitted || !ObservedStrategy.ready state.agent then .wait
  else match FairGoalScheduling.select state.goals with
    | none => .idle
    | some goal => .goal goal

def capture (cfg : Config) (admitted : Bool) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey)
    (changes : List IterArchitecture.Transformation) : State :=
  if admitted then
    match FairGoalScheduling.select state.goals with
    | none => state
    | some goal =>
        if cfg.key (goal.id, goal.round) = focus ∧
            ObservedStrategy.canCapture state.agent now focus = true then
          { agent := ObservedStrategy.capture state.agent now focus changes
            goals := FairGoalScheduling.charge goal.id 1 state.goals }
        else state
  else state

def step (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (admitted : Bool) (state : State) : GoalSystem.Event → State
  | .operational (.captured now focus changes) => capture cfg admitted state now focus changes
  | event => GoalSystem.step cfg checks state event

def run (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (admitted : Bool) : State → List GoalSystem.Event → State
  | state, [] => state
  | state, event :: rest => run cfg checks admitted (step cfg checks admitted state event) rest

theorem input_preempts (state : State) (admitted : Bool)
    (pending : state.agent.requests.inbox.isEmpty = false) :
    next state admitted = .input := by simp [next, pending]

theorem admission_denial_stutters (cfg : Config) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes) :
    capture cfg false state now focus changes = state := by simp [capture]

theorem host_denial_stutters (cfg : Config) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes) (admitted : Bool)
    (denied : ObservedStrategy.canCapture state.agent now focus = false) :
    capture cfg admitted state now focus changes = state := by
  cases admitted with
  | false => rfl
  | true =>
      cases selected : FairGoalScheduling.select state.goals <;> simp [capture, selected, denied]

theorem capture_contract (cfg : Config) (state : State) (goal : Goal) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes)
    (selected : FairGoalScheduling.select state.goals = some goal)
    (matching : cfg.key (goal.id, goal.round) = focus)
    (allowed : ObservedStrategy.canCapture state.agent now focus = true) :
    (capture cfg true state now focus changes).agent =
      ObservedStrategy.capture state.agent now focus changes ∧
    (capture cfg true state now focus changes).goals =
      FairGoalScheduling.charge goal.id 1 state.goals := by
  simp [capture, selected, matching, allowed]

theorem capture_charges_exactly_one_account (cfg : Config) (state : State) (goal : Goal) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes)
    (unique : FairGoalScheduling.UniqueIds state.goals)
    (selected : FairGoalScheduling.select state.goals = some goal)
    (matching : cfg.key (goal.id, goal.round) = focus)
    (allowed : ObservedStrategy.canCapture state.agent now focus = true) :
    FairGoalScheduling.totalService (capture cfg true state now focus changes).goals =
      FairGoalScheduling.totalService state.goals + 1 := by
  rw [(capture_contract cfg state goal now focus changes selected matching allowed).2]
  exact FairGoalScheduling.charge_exactly_one_account state.goals goal 1 unique
    (FairGoalScheduling.selection_contract state.goals goal selected).1

theorem capture_preserves_request_ledger (cfg : Config) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes) (admitted : Bool) :
    (capture cfg admitted state now focus changes).agent.requests = state.agent.requests := by
  cases admitted with
  | false => rfl
  | true =>
      cases selected : FairGoalScheduling.select state.goals with
      | none => simp [capture, selected]
      | some goal =>
          simp only [capture, selected, ↓reduceIte]
          split
          · exact ObservedStrategy.capture_preserves_request_ledger state.agent now focus changes
          · rfl

theorem pending_capture_stutters (cfg : Config) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes) (admitted : Bool)
    (pending : state.agent.pending ≠ none) :
    capture cfg admitted state now focus changes = state := by
  apply host_denial_stutters
  simp [ObservedStrategy.canCapture_eq, ObservedStrategy.ready, pending]

theorem duplicate_capture_stutters (cfg : Config) (state : State) (now : Int)
    (focus : ConversationContinuation.RequestKey) (changes) (admitted : Bool) :
    capture cfg admitted (capture cfg admitted state now focus changes) now focus changes =
      capture cfg admitted state now focus changes := by
  cases admitted with
  | false => rfl
  | true =>
      cases selected : FairGoalScheduling.select state.goals with
      | none => simp [capture, selected]
      | some goal =>
          by_cases accepted : cfg.key (goal.id, goal.round) = focus ∧
              ObservedStrategy.canCapture state.agent now focus = true
          · apply pending_capture_stutters
            rw [(capture_contract cfg state goal now focus changes selected accepted.1 accepted.2).1]
            rw [(ObservedStrategy.admitted_capture_submits_exactly_one_attempt
              state.agent now focus changes accepted.2).1]
            simp
          · have unchanged : capture cfg true state now focus changes = state := by
              simp [capture, selected, accepted]
            simp [unchanged]

theorem cycle_acknowledgement_keeps_spent_service (cfg : Config) (checks)
    (state : State) (report : Report) :
    (GoalSystem.acknowledge cfg checks state report).goals.map Goal.service =
      state.goals.map Goal.service := by
  unfold GoalSystem.acknowledge
  split
  · simp only [List.map_map]
    congr 1
    funext goal
    simp only [Function.comp_apply]
    split <;> rfl
  · rfl

theorem control_events_preserve_service (cfg : Config) (checks) (admitted : Bool)
    (state : State) (event : ObservedStrategy.OperationalEvent)
    (notCapture : ∀ now focus changes, event ≠ .captured now focus changes) :
    (step cfg checks admitted state (.operational event)).goals = state.goals := by
  cases event <;> try rfl
  exact False.elim (notCapture _ _ _ rfl)

theorem step_preserves_other_unfinished_work (cfg : Config) (checks) (admitted : Bool)
    (state : State) (event : GoalSystem.Event) (key : ConversationContinuation.RequestKey)
    (active : state.agent.requests.commitments key = .active)
    (unrelated : GoalSystem.NotFor key event) :
    (step cfg checks admitted state event).agent.requests.commitments key = .active := by
  cases event with
  | elapsed ticks => exact active
  | serviced report =>
      exact (GoalSystem.acknowledgement_preserves_other_work cfg checks state report key unrelated).trans active
  | operational event =>
      cases event with
      | captured now focus changes =>
          simpa only [step, capture_preserves_request_ledger] using active
      | _ => exact ObservedStrategy.operational_step_preserves_active_work state.agent _ key active

theorem arbitrary_trace_preserves_other_unfinished_work (cfg : Config) (checks) (admitted : Bool)
    (state : State) (events : List GoalSystem.Event) (key : ConversationContinuation.RequestKey)
    (active : state.agent.requests.commitments key = .active)
    (unrelated : ∀ event ∈ events, GoalSystem.NotFor key event) :
    (run cfg checks admitted state events).agent.requests.commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih =>
      exact ih _ (step_preserves_other_unfinished_work cfg checks admitted state event key active
        (unrelated event List.mem_cons_self))
        (fun e h => unrelated e (List.mem_cons_of_mem _ h))

end FairGoalStrategy
