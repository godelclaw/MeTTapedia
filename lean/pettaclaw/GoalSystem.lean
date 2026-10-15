import ObservedStrategy

/-!
# Shared goal records and checked completion

Research, maintenance and goal review use the same goal records.
Urgency is a configured base plus elapsed time since the last checked cycle.
Blocked and finished goals are not eligible; a recurring goal becomes eligible
after its configured interval. Ties retain the recorded queue order.

Scheduling metadata is attached to the existing protected request ledger.
Completing a cycle uses that ledger's observed-result checker. A one-shot goal
then finishes; a recurring goal resets its age and receives a fresh cycle key.
Selection alone grants no authority, spends no budget and completes no work.

The urgency-only selector below remains a reference policy; its conditional
selection theorem is not starvation freedom. `FairGoalScheduling` adds
weighted service over these same records, and `FairGoalStrategy` charges each
admitted provider attempt without changing the completion rule.

Host obligations: goal IDs are unique; cycle keys are fresh and disjoint from
other requests; elapsed time and queue metadata are faithfully checkpointed;
checker acceptance establishes the actual cycle outcome; revision checks and
updates are atomic. Ordinary progress should be represented by suitably sized
cycles. Repeatedly choosing a goal without verified progress does not reset
its age. Growing urgency alone cannot guarantee service under unlimited
competing urgency, permanent blocking or resource denial.
-/

namespace GoalSystem

open Mettapedia.CogArch.Agent

structure Config where
  key : Nat × Nat → ConversationContinuation.RequestKey
  key_injective : Function.Injective key

inductive Recurrence where
  | once
  | every (interval : Nat)
deriving Repr, DecidableEq

structure Goal where
  id : Nat
  baseUrgency : Nat := 0
  recurrence : Recurrence := .once
  age : Nat := 0
  round : Nat := 0
  blocked : Bool := false
  finished : Bool := false
  /-- Configured relative share. Zero disables autonomous service. -/
  share : Nat := 1
  /-- Attention already allocated, independent of verified achievement. -/
  service : Nat := 0
deriving Repr, DecidableEq

def urgency (goal : Goal) : Nat := goal.baseUrgency + goal.age

def eligible (goal : Goal) : Bool :=
  !goal.blocked && !goal.finished &&
    match goal.recurrence with
    | .once => true
    | .every interval => decide (interval ≤ goal.age)

def advance (elapsed : Nat) (goal : Goal) : Goal :=
  if goal.finished then goal else { goal with age := goal.age + elapsed }

/-- Maximum eligible urgency, retaining queue order on ties. The selector
does not inspect a goal's name or purpose. -/
def select : List Goal → Option Goal
  | [] => none
  | goal :: goals =>
      if eligible goal then
        match select goals with
        | none => some goal
        | some later => if urgency later ≤ urgency goal then some goal else some later
      else select goals

structure State where
  agent : ObservedStrategy.State
  goals : List Goal := []

/-- `idle` means this queue has no eligible candidate. It does not certify
that the protected request ledger contains no unfinished work. -/
inductive Choice where
  | input | wait | idle | goal (selected : Goal)
deriving Repr, DecidableEq

def next (state : State) (admitted : Bool) : Choice :=
  if !state.agent.requests.inbox.isEmpty then .input
  else if !admitted || !ObservedStrategy.ready state.agent then .wait
  else match select state.goals with
    | none => .idle
    | some goal => .goal goal

structure Report where
  goal : Nat
  revision : Nat
  receipt : ConversationContinuation.Receipt
deriving Repr, DecidableEq

def canAcknowledge (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (agent : ObservedStrategy.State) (goal : Goal) (report : Report) : Bool :=
  !goal.blocked && !goal.finished && ObservedStrategy.completionReady agent &&
    decide (report.goal = goal.id ∧ report.revision = agent.revision ∧
      report.receipt.ticket.request = cfg.key (goal.id, goal.round)) &&
    ConversationContinuation.canComplete checks agent.requests
      (cfg.key (goal.id, goal.round)) report.receipt

def afterService (goal : Goal) : Goal :=
  { goal with
    age := 0
    round := goal.round + 1
    finished := match goal.recurrence with | .once => true | .every _ => false }

def acknowledge (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) (report : Report) : State :=
  if state.goals.any (fun goal => canAcknowledge cfg checks state.agent goal report) then
    { agent := ObservedStrategy.finish checks state.agent report.receipt.ticket.request report.receipt
      goals := state.goals.map (fun goal =>
        if canAcknowledge cfg checks state.agent goal report then afterService goal else goal) }
  else state

inductive Event where
  | elapsed (ticks : Nat)
  | serviced (report : Report)
  | operational (event : ObservedStrategy.OperationalEvent)

def step (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool)
    (state : State) : Event → State
  | .elapsed ticks => { state with goals := state.goals.map (advance ticks) }
  | .serviced report => acknowledge cfg checks state report
  | .operational event => { state with agent := ObservedStrategy.step state.agent event }

def run (cfg : Config)
    (checks : ConversationContinuation.RequestKey → ConversationContinuation.Receipt → Bool) :
    State → List Event → State
  | state, [] => state
  | state, event :: events => run cfg checks (step cfg checks state event) events

theorem urgency_monotone (elapsed : Nat) (goal : Goal) :
    urgency goal ≤ urgency (advance elapsed goal) := by
  simp only [advance]
  split <;> simp [urgency]

theorem urgency_grows (elapsed : Nat) (goal : Goal) (unfinished : goal.finished = false) :
    urgency (advance elapsed goal) = urgency goal + elapsed := by
  simp [advance, unfinished, urgency, Nat.add_assoc]

theorem elapsed_partition_independent (a b : Nat) (goal : Goal) :
    advance b (advance a goal) = advance (a + b) goal := by
  by_cases finished : goal.finished = true
  · simp [advance, finished]
  · have unfinished : goal.finished = false := Bool.eq_false_iff.mpr finished
    simp [advance, unfinished, Nat.add_assoc]

theorem recurring_becomes_eligible (goal : Goal) (interval elapsed : Nat)
    (recurring : goal.recurrence = .every interval)
    (unblocked : goal.blocked = false) (unfinished : goal.finished = false)
    (enough : interval ≤ elapsed) :
    eligible (advance elapsed goal) = true := by
  simp only [advance, unfinished, Bool.false_eq_true, ↓reduceIte, eligible,
    unblocked, Bool.not_false, Bool.true_and, recurring, decide_eq_true_eq]
  omega

theorem blocked_not_eligible (goal : Goal) (blocked : goal.blocked = true) :
    eligible goal = false := by simp [eligible, blocked]

theorem finished_not_eligible (goal : Goal) (finished : goal.finished = true) :
    eligible goal = false := by simp [eligible, finished]

theorem select_none_iff (goals : List Goal) :
    select goals = none ↔ ∀ goal ∈ goals, eligible goal = false := by
  induction goals with
  | nil => simp [select]
  | cons goal goals ih =>
      cases available : eligible goal with
      | false => simpa [select, available] using ih
      | true =>
          cases later : select goals <;> simp [select, available, later]
          split <;> simp

/-- Every selected goal is eligible and has maximal urgency among all
eligible goals. This is shared by every goal purpose and recurrence. -/
theorem selection_contract (goals : List Goal) (chosen : Goal)
    (selected : select goals = some chosen) :
    chosen ∈ goals ∧ eligible chosen = true ∧
      ∀ goal ∈ goals, eligible goal = true → urgency goal ≤ urgency chosen := by
  induction goals generalizing chosen with
  | nil => simp [select] at selected
  | cons head tail ih =>
      cases available : eligible head with
      | false =>
          have found : select tail = some chosen := by simpa [select, available] using selected
          obtain ⟨member, valid, maximum⟩ := ih chosen found
          refine ⟨List.mem_cons_of_mem head member, valid, ?_⟩
          intro goal member eligibleGoal
          rcases List.mem_cons.mp member with equal | member
          · subst goal; simp [available] at eligibleGoal
          · exact maximum goal member eligibleGoal
      | true =>
          cases later : select tail with
          | none =>
              have equal : head = chosen := by simpa [select, available, later] using selected
              subst chosen
              refine ⟨List.mem_cons_self, available, ?_⟩
              intro goal member eligibleGoal
              rcases List.mem_cons.mp member with equal | member
              · subst goal; exact Nat.le_refl _
              · have invalid := (select_none_iff tail).mp later goal member
                simp [invalid] at eligibleGoal
          | some best =>
              obtain ⟨member, valid, maximum⟩ := ih best later
              by_cases wins : urgency best ≤ urgency head
              · have equal : head = chosen := by
                  simpa [select, available, later, wins] using selected
                subst chosen
                refine ⟨List.mem_cons_self, available, ?_⟩
                intro goal member eligibleGoal
                rcases List.mem_cons.mp member with equal | member
                · subst goal; exact Nat.le_refl _
                · exact Nat.le_trans (maximum goal member eligibleGoal) wins
              · have equal : best = chosen := by
                  simpa [select, available, later, wins] using selected
                subst chosen
                refine ⟨List.mem_cons_of_mem head member, valid, ?_⟩
                intro goal member eligibleGoal
                rcases List.mem_cons.mp member with equal | member
                · subst goal; omega
                · exact maximum goal member eligibleGoal

theorem strict_maximum_is_selected (goals : List Goal) (goal : Goal)
    (member : goal ∈ goals) (valid : eligible goal = true)
    (greatest : ∀ other ∈ goals, eligible other = true → other ≠ goal →
      urgency other < urgency goal) :
    select goals = some goal := by
  cases selected : select goals with
  | none =>
      have invalid := (select_none_iff goals).mp selected goal member
      simp [invalid] at valid
  | some chosen =>
      obtain ⟨chosenMember, chosenValid, maximum⟩ := selection_contract goals chosen selected
      by_cases equal : chosen = goal
      · simp [equal]
      · have upper := maximum goal member valid
        have lower := greatest chosen chosenMember chosenValid equal
        omega

/-- A finite competitor bound yields a concrete selection condition.
The bound concerns competitors at this boundary, including their ageing;
it is not an assumption that the queue remains unchanged forever. -/
theorem ageing_wins_bounded_competition (goals : List Goal) (goal : Goal) (bound : Nat)
    (member : goal ∈ goals) (valid : eligible goal = true) (oldEnough : bound < goal.age)
    (bounded : ∀ other ∈ goals, eligible other = true → other ≠ goal →
      urgency other ≤ bound) :
    select goals = some goal := by
  apply strict_maximum_is_selected goals goal member valid
  intro other member valid different
  have upper := bounded other member valid different
  simp only [urgency] at upper ⊢
  omega

theorem stable_tie_uses_queue_order (first later : Goal)
    (firstValid : eligible first = true) (laterValid : eligible later = true)
    (tied : urgency first = urgency later) :
    select [first, later] = some first := by
  simp [select, firstValid, laterValid, tied]

theorem unread_input_preempts (state : State) (admitted : Bool)
    (unread : state.agent.requests.inbox.isEmpty = false) :
    next state admitted = .input := by simp [next, unread]

theorem admission_denial_waits (state : State)
    (clear : state.agent.requests.inbox.isEmpty = true) :
    next state false = .wait := by simp [next, clear]

theorem unavailable_thought_waits (state : State) (admitted : Bool)
    (clear : state.agent.requests.inbox.isEmpty = true)
    (pending : ObservedStrategy.ready state.agent = false) :
    next state admitted = .wait := by simp [next, clear, pending]

theorem admitted_selection_is_generic (state : State) (goal : Goal)
    (clear : state.agent.requests.inbox.isEmpty = true)
    (ready : ObservedStrategy.ready state.agent = true)
    (selected : select state.goals = some goal) :
    next state true = .goal goal := by simp [next, clear, ready, selected]

theorem acknowledgement_contract (cfg : Config) (checks)
    (agent : ObservedStrategy.State) (goal : Goal) (report : Report) :
    canAcknowledge cfg checks agent goal report = true ↔
      goal.blocked = false ∧ goal.finished = false ∧ ObservedStrategy.completionReady agent = true ∧
      (report.goal = goal.id ∧ report.revision = agent.revision ∧
        report.receipt.ticket.request = cfg.key (goal.id, goal.round)) ∧
      ConversationContinuation.canComplete checks agent.requests
        (cfg.key (goal.id, goal.round)) report.receipt = true := by
  simp [canAcknowledge, Bool.and_eq_true, and_assoc]

theorem unsettled_effects_block_completion (cfg : Config) (checks)
    (agent : ObservedStrategy.State) (goal : Goal) (report : Report)
    (unsettled : ObservedStrategy.effectsReady agent = false) :
    canAcknowledge cfg checks agent goal report = false := by
  simp [canAcknowledge, ObservedStrategy.completionReady, unsettled]

theorem checked_cycle_finishes_its_ledger_request (cfg : Config) (checks)
    (agent : ObservedStrategy.State) (goal : Goal) (report : Report)
    (checked : canAcknowledge cfg checks agent goal report = true) :
    (ObservedStrategy.finish checks agent report.receipt.ticket.request report.receipt).requests.commitments
        report.receipt.ticket.request = .discharged ⟨.achieved, .result report.receipt⟩ := by
  have facts := (acknowledgement_contract cfg checks agent goal report).mp checked
  have readyFacts : agent.requests.interrupted = false ∧ agent.requests.inbox.isEmpty = true ∧
      agent.pending = none ∧ agent.requests.phase = .ready ∧ agent.dispatch = none := by
    simpa [ObservedStrategy.completionReady, ObservedStrategy.ready,
      ObservedStrategy.effectsReady, Bool.and_eq_true, and_assoc] using facts.2.2.1
  have completing := facts.2.2.2.2
  have active := (ConversationContinuation.completion_requires_matching_observed_success
    checks agent.requests (cfg.key (goal.id, goal.round)) report.receipt completing).1
  rw [facts.2.2.2.1.2.2]
  simp [ObservedStrategy.finish, readyFacts.2.1, readyFacts.2.2.1, readyFacts.2.2.2.1,
    ConversationContinuation.complete, completing, ConversationContinuation.setCommitment,
    GoalCommitment.step, active]

theorem cycle_reset_is_generic (goal : Goal) :
    (afterService goal).age = 0 ∧ (afterService goal).round = goal.round + 1 ∧
      (afterService goal).id = goal.id := by simp [afterService]

theorem once_finishes (goal : Goal) (once : goal.recurrence = .once) :
    (afterService goal).finished = true := by simp [afterService, once]

theorem recurring_rearms (goal : Goal) (interval : Nat)
    (recurring : goal.recurrence = .every interval) (positive : 0 < interval)
    (unblocked : goal.blocked = false) :
    (afterService goal).finished = false ∧ eligible (afterService goal) = false := by
  simp [afterService, eligible, recurring, unblocked, Nat.not_le_of_gt positive]

theorem old_receipt_cannot_pay_another_cycle (cfg : Config) (checks)
    (agent laterAgent : ObservedStrategy.State) (goal later : Goal) (report : Report)
    (checked : canAcknowledge cfg checks agent goal report = true)
    (different : (later.id, later.round) ≠ (goal.id, goal.round)) (newRevision : Nat) :
    canAcknowledge cfg checks laterAgent later { report with revision := newRevision } = false := by
  have original := ((acknowledgement_contract cfg checks agent goal report).mp checked).2.2.2.1.2.2
  by_cases accepted : canAcknowledge cfg checks laterAgent later
      { report with revision := newRevision } = true
  · have reused := ((acknowledgement_contract cfg checks laterAgent later
        { report with revision := newRevision }).mp accepted).2.2.2.1.2.2
    exact False.elim (different (cfg.key_injective (reused.symm.trans original)))
  · exact Bool.eq_false_iff.mpr accepted

theorem failed_acknowledgement_stutters (cfg : Config) (checks) (state : State) (report : Report)
    (failed : state.goals.any (fun goal => canAcknowledge cfg checks state.agent goal report) = false) :
    acknowledge cfg checks state report = state := by simp [acknowledge, failed]

theorem acknowledgement_preserves_other_work (cfg : Config) (checks)
    (state : State) (report : Report) (key : ConversationContinuation.RequestKey)
    (different : key ≠ report.receipt.ticket.request) :
    (acknowledge cfg checks state report).agent.requests.commitments key =
      state.agent.requests.commitments key := by
  unfold acknowledge
  split
  · exact ObservedStrategy.finish_cannot_discharge_another_request
      checks state.agent report.receipt.ticket.request key report.receipt different
  · rfl

theorem bookkeeping_preserves_identity (cfg : Config) (checks) (state : State) (event : Event) :
    (step cfg checks state event).goals.map Goal.id = state.goals.map Goal.id := by
  cases event with
  | elapsed ticks =>
      simp only [step, List.map_map]
      congr 1
      funext goal
      simp only [Function.comp_apply, advance]
      split <;> rfl
  | operational event => rfl
  | serviced report =>
      simp only [step, acknowledge]
      split
      · simp only [List.map_map]
        congr 1
        funext goal
        simp only [Function.comp_apply]
        split <;> rfl
      · rfl

theorem time_preserves_agent (cfg : Config) (checks) (state : State) (ticks : Nat) :
    (step cfg checks state (.elapsed ticks)).agent = state.agent := by rfl

theorem operational_step_preserves_goals (cfg : Config) (checks)
    (state : State) (event : ObservedStrategy.OperationalEvent) :
    (step cfg checks state (.operational event)).goals = state.goals := by rfl

def NotFor (key : ConversationContinuation.RequestKey) : Event → Prop
  | .serviced report => key ≠ report.receipt.ticket.request
  | _ => True

theorem mixed_trace_preserves_other_unfinished_work (cfg : Config) (checks)
    (state : State) (events : List Event) (key : ConversationContinuation.RequestKey)
    (active : state.agent.requests.commitments key = .active)
    (unrelated : ∀ event ∈ events, NotFor key event) :
    (run cfg checks state events).agent.requests.commitments key = .active := by
  induction events generalizing state with
  | nil => exact active
  | cons event events ih =>
      apply ih
      · cases event with
        | elapsed ticks => exact active
        | operational event =>
            exact ObservedStrategy.operational_step_preserves_active_work state.agent event key active
        | serviced report =>
            exact (acknowledgement_preserves_other_work cfg checks state report key
              (unrelated (.serviced report) (List.mem_cons_self))).trans active
      · intro event member
        exact unrelated event (List.mem_cons_of_mem _ member)

end GoalSystem
