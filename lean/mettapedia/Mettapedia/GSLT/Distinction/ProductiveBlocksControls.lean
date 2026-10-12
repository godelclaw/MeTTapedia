import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Distinction.BlockTransportControls

/-!
# Controls for productive blocks

* **Divergence and deadlock are observed** (`wedge_observations`,
  `blocks_cannot_separate`, `status_separates`).  A finished state, an
  infinite silent loop and a silent stuck state have no blocks, so the block
  system relates them all.  Their statuses differ: only the first finishes.
  Neither the loop nor the stuck state admits a progress premise
  (`spinning_not_productive`, `wedged_not_productive`).
* **Resumption, not restart** (`duplicate_delivery_control`,
  `repeated_effect_control`).  Resuming the saved residual delivers each
  answer once.  Restarting re-delivers an answer, and re-commits an effect
  while the answer bags agree.
* **Accounts are observations only when declared** (`account_control`).
* **Relabeling retains execution** (`relabeled_line_resumption`,
  `relabeling_retains_occurrences`, `masked_call_retains_saved_continuation`).
  Lossy label maps keep the full residual, transition charges and occurrence
  count, but cannot identify which committed effect occurred
  (`lossy_observation_cannot_identify_effects`).
* **Callbacks** (`callback_events_visible`, `cancellation_visible`,
  `external_erases_callback`).  A reentrant callback's effect appears in the
  closed trace; classifying the callback step as external makes the blocks of
  two different callbacks identical.
* **Compiled blocks settle** (`four_prefix_settles`): the four-step lowering
  of one exchange has bounded administrative work, so every primitive prefix
  is a source run followed by at most three administrative steps.
* **Relation-level transport** (`check_interpret_final`,
  `spinning_interpreter_not_simulated`).  A one-step checker and a three-step
  interpreter are related by a relation that is not a function, with cost
  three forward and one backward; their final observations coincide.  An
  interpreter that spins silently is related to no such checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation Event answerBag)

/-! ## Divergence and deadlock -/

inductive Wedge where
  | done
  | spinning
  | wedged
  deriving DecidableEq

/-- A finished state, an infinite silent loop and a stuck state. -/
def wedgeMachine : Machine Wedge ℕ Unit Empty where
  step
    | .done => some (.finish ())
    | .spinning => some (.silent .spinning)
    | .wedged => none

theorem wedge_observations (fuel : ℕ) :
    wedgeMachine.observe (fuel + 1) .done = ⟨[], .finished ()⟩ ∧
      wedgeMachine.observe fuel .spinning = ⟨[], .incomplete⟩ ∧
      wedgeMachine.observe fuel .wedged = ⟨[], .incomplete⟩ :=
  ⟨rfl,
    wedgeMachine.silent_region_incomplete (· = .spinning)
      (by rintro _ rfl; exact ⟨.spinning, rfl, rfl⟩) fuel _ rfl,
    wedgeMachine.stuck_incomplete .wedged rfl fuel⟩

theorem no_blocks (events : List ℕ) (state next : Wedge) :
    ¬ wedgeMachine.reading.Block events state next := by
  rintro ⟨middle, _, completes⟩
  change wedgeMachine.step middle = _ at completes
  cases middle <;> simp [wedgeMachine] at completes

/-- **Blocks cannot separate finishing, looping and deadlock.** -/
theorem blocks_cannot_separate (left right : Wedge) :
    wedgeMachine.reading.blockSystem.Bisimilar left right := by
  refine ⟨fun _ _ => True, ⟨?_, ?_, ?_⟩, trivial⟩
  · intro _ _ _ _ _ block
    exact absurd block (no_blocks _ _ _)
  · intro _ _ _ _ _ block
    exact absurd block (no_blocks _ _ _)
  · intro _ _ _ atom
    exact atom.elim

/-- **The status separates them.** -/
theorem status_separates :
    ¬ wedgeMachine.statusSystem.Bisimilar .done .spinning ∧
      ¬ wedgeMachine.statusSystem.Bisimilar .done .wedged := by
  constructor <;>
  · rintro ⟨relation, ⟨_, _, atoms⟩, related⟩
    have finished := (atoms related (.finished ())).mp rfl
    simp [Machine.statusSystem, Machine.observe, Machine.run, wedgeMachine,
      Outcome.status] at finished

theorem spinning_not_productive : IsEmpty wedgeMachine.Productive :=
  wedgeMachine.not_productive_of_silent_region (· = .spinning)
    (by rintro _ rfl; exact ⟨.spinning, rfl, rfl⟩) .spinning rfl

theorem wedged_not_productive : IsEmpty wedgeMachine.Productive :=
  ⟨fun productive => productive.moves .wedged rfl⟩

theorem spinning_run (fuel : Nat) :
    wedgeMachine.run fuel .spinning = ([], .exhausted .spinning) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [Machine.run, wedgeMachine] using ih

theorem spinning_diverges : wedgeMachine.DivergesWithin .spinning := by
  intro fuel
  exact ⟨.spinning, congrArg Prod.snd (spinning_run fuel)⟩

theorem wedged_does_not_diverge : ¬ wedgeMachine.DivergesWithin .wedged :=
  wedgeMachine.not_divergesWithin_of_stuck rfl

/-- The coarse observation deliberately forgets the distinction that full
finite outcomes retain. Neither incompleteness nor absence of events means
that computation can continue. -/
theorem same_observation_different_divergence (fuel : Nat) :
    wedgeMachine.observe fuel .spinning = wedgeMachine.observe fuel .wedged ∧
      wedgeMachine.DivergesWithin .spinning ∧ ¬ wedgeMachine.DivergesWithin .wedged :=
  ⟨(wedge_observations fuel).2.1.trans (wedge_observations fuel).2.2.symm,
    spinning_diverges, wedged_does_not_diverge⟩

theorem spinning_resumption_diverges (fuel : Nat) :
    ∃ residual, wedgeMachine.run fuel .spinning = ([], .exhausted residual) ∧
      wedgeMachine.DivergesWithin residual :=
  ⟨.spinning, spinning_run fuel, spinning_diverges⟩

/-! ## Resumption, not restart -/

inductive Line where
  | start
  | admin
  | middle
  | last
  deriving DecidableEq

abbrev LineEvent := Event ℕ String Unit

/-- One administrative step, two publications, and a finish. -/
def lineMachine (first second : LineEvent) : Machine Line LineEvent Unit Empty where
  step
    | .start => some (.silent .admin)
    | .admin => some (.publish [first] .middle)
    | .middle => some (.publish [second] .last)
    | .last => some (.finish ())

/-- The line is productive: one administrative step, then visible work. -/
def lineProductive (first second : LineEvent) : (lineMachine first second).Productive where
  rank
    | .start => 1
    | _ => 0
  silent_decreases := by
    intro state next stepped
    cases state <;> simp [lineMachine] at stepped
    subst stepped
    decide
  moves state := by cases state <;> simp [lineMachine]

theorem line_paused (first second : LineEvent) :
    (lineMachine first second).run 2 .start = ([first], .exhausted .middle) :=
  rfl

/-- **Duplicate delivery**: resuming the residual delivers each answer once;
restarting re-delivers the first. -/
theorem duplicate_delivery_control :
    let machine := lineMachine (.answer 1) (.answer 2)
    (machine.run 2 .start).1 ++ (machine.run 3 .middle).1 = (machine.run 5 .start).1 ∧
      (machine.run 5 .start).1 = [.answer 1, .answer 2] ∧
      (machine.run 2 .start).1 ++ (machine.run 5 .start).1 = [.answer 1, .answer 1, .answer 2] := by
  refine ⟨?_, rfl, rfl⟩
  have resumed := (lineMachine (.answer 1) (.answer 2)).established_and_pending 2 3 .start .middle
    [.answer 1] rfl
  rw [show 2 + 3 = 5 from rfl] at resumed
  rw [resumed]
  rfl

/-- **A repeated committed effect**: restarting re-commits the effect, while the
answer bags of restart and resumption agree. -/
theorem repeated_effect_control :
    let machine := lineMachine (.effect "write") (.answer 1)
    (machine.run 2 .start).1 ++ (machine.run 5 .start).1 = [.effect "write", .effect "write", .answer 1] ∧
      (machine.run 5 .start).1 = [.effect "write", .answer 1] ∧
      answerBag ((machine.run 2 .start).1 ++ (machine.run 5 .start).1) =
        answerBag (machine.run 5 .start).1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Observation relabeling -/

/-- Retain answer and fault identity but hide the name of each effect. -/
def maskEffect : LineEvent → LineEvent
  | .answer value => .answer value
  | .effect _ => .effect "masked"
  | .fault failure => .fault failure

/-- Hiding labels preserves the ordered occurrences and complete residual. -/
theorem relabeling_retains_occurrences :
    ((lineMachine (.effect "first") (.effect "second")).relabel maskEffect id id).run 3 .start =
      ([.effect "masked", .effect "masked"], .exhausted .last) := rfl

/-- Even a one-element event carrier retains both emitted occurrences. -/
theorem constant_event_map_keeps_multiplicity :
    ((lineMachine (.answer 1) (.answer 2)).relabel (fun _ => ()) id id).run 3 .start =
      ([(), ()], .exhausted .last) := rfl

/-- Equal masked runs do not establish the identity of the original effects. -/
theorem lossy_observation_cannot_identify_effects :
    ((lineMachine (.effect "write-A") (.answer 1)).run 4 .start).1 ≠
        ((lineMachine (.effect "write-B") (.answer 1)).run 4 .start).1 ∧
      ((lineMachine (.effect "write-A") (.answer 1)).relabel maskEffect id id).run 4 .start =
        ((lineMachine (.effect "write-B") (.answer 1)).relabel maskEffect id id).run 4 .start :=
  ⟨by decide, rfl⟩

theorem relabeled_line_resumption (first second : LineEvent) (fuel : ℕ) :
    ((lineMachine first second).relabel maskEffect id id).run (2 + fuel) .start =
      ([maskEffect first] ++ (((lineMachine first second).relabel maskEffect id id).run fuel .middle).1,
        (((lineMachine first second).relabel maskEffect id id).run fuel .middle).2) := by
  simpa only [List.map_cons, List.map_nil] using
    (lineMachine first second).relabel_resumed maskEffect id id 2 fuel .start .middle [first]
      (line_paused first second)

theorem relabeled_line_accounts (first second : LineEvent) (price : Line → ℕ) (fuel : ℕ) :
    ((lineMachine first second).relabel maskEffect id id).spent price (2 + fuel) .start =
      (lineMachine first second).spent price 2 .start +
        ((lineMachine first second).relabel maskEffect id id).spent price fuel .middle :=
  (lineMachine first second).relabel_resumed_accounts maskEffect id id price 2 fuel .start .middle [first]
    (line_paused first second)

theorem relabeled_line_uses_original_rank (first second : LineEvent) (state : Line) :
    ((lineProductive first second).relabeled maskEffect id id).rank state =
      (lineProductive first second).rank state := rfl

/-- Reversible event tags reflect exact runs, including their residual states. -/
theorem injective_event_tags_reflect_runs (first second first' second' : LineEvent)
    (fuel fuel' : ℕ) (state state' : Line) :
    ((lineMachine first second).relabel (fun event => (event, ())) id id).run fuel state =
        ((lineMachine first' second').relabel (fun event => (event, ())) id id).run fuel' state' ↔
      (lineMachine first second).run fuel state = (lineMachine first' second').run fuel' state' :=
  (lineMachine first second).relabel_runs_eq_iff (lineMachine first' second')
    (fun event => (event, ())) id id
    (fun _ _ equal => congrArg Prod.fst equal) (fun _ _ equal => equal) (fun _ _ equal => equal)
    fuel fuel' state state'

/-- Hiding every label cannot turn a silent divergent computation into a final one. -/
theorem coarse_observation_keeps_divergence (fuel : ℕ) :
    ¬ ((wedgeMachine.relabel (fun _ => ()) (fun _ => ()) id).observe fuel .spinning).status.Final := by
  rw [wedgeMachine.relabel_final_iff]
  rw [(wedge_observations fuel).2.1]
  exact False.elim

/-! ## Accounts -/

inductive Pace where
  | slow
  | slowFinal
  | fast
  deriving DecidableEq

def paceMachine : Machine Pace ℕ Unit Empty where
  step
    | .slow => some (.silent .slowFinal)
    | .slowFinal => some (.finish ())
    | .fast => some (.finish ())

/-- **Equal observations, different accounts**: an account is an observation
only when the observer declares it. -/
theorem account_control :
    paceMachine.observe 2 .slow = paceMachine.observe 2 .fast ∧
      paceMachine.spent (fun _ => 1) 2 .slow = 2 ∧ paceMachine.spent (fun _ => 1) 2 .fast = 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Callbacks -/

inductive Call where
  | start
  | after
  | done
  deriving DecidableEq

/-- Call out, then publish an answer, then finish. -/
def caller : Machine Call LineEvent Unit String where
  step
    | .start => some (.call "lookup" .after)
    | .after => some (.publish [.answer 1] .done)
    | .done => some (.finish ())

/-- Visible call and reply events; a cancelled or faulted call skips the
continuation's publication. -/
def protocol : Callback Call LineEvent String ℕ Unit where
  callEvent request := .effect request
  replyEvent
    | .returned _ => .effect "returned"
    | .faulted _ => .fault ()
    | .cancelled => .effect "cancelled"
  resume saved
    | .returned _ => saved
    | _ => .done

/-- A callback that reenters and commits its own effect. -/
def reentrant : Environment String LineEvent ℕ Unit := fun _ => ([.effect "reentrant"], .returned 0)

/-- A callback without its own events. -/
def plain : Environment String LineEvent ℕ Unit := fun _ => ([], .returned 0)

def cancelling : Environment String LineEvent ℕ Unit := fun _ => ([], .cancelled)

theorem caller_suspends : caller.run 1 .start = ([], .suspended "lookup" .after) :=
  rfl

/-- A retained external request is a boundary awaiting a response, even
though it has not finished the surrounding program. -/
theorem pending_request_does_not_diverge : ¬ caller.DivergesWithin .start := by
  intro diverges
  obtain ⟨residual, remains⟩ := diverges 1
  rw [caller_suspends] at remains
  cases remains

/-- A hidden request still suspends at the exact original continuation. -/
theorem masked_call_retains_saved_continuation :
    (caller.relabel maskEffect id (fun _ => ())).run 1 .start =
      ([], .suspended () .after) := by
  rw [caller.run_relabel, caller_suspends]
  rfl

/-- **The callback's own effect is visible in the closed trace.** -/
theorem callback_events_visible :
    ((caller.close protocol reentrant).run 3 .start).1 =
        [.effect "lookup", .effect "reentrant", .effect "returned", .answer 1] ∧
      ((caller.close protocol plain).run 3 .start).1 =
        [.effect "lookup", .effect "returned", .answer 1] :=
  ⟨rfl, rfl⟩

/-- **Cancellation is a visible event, and the saved continuation decides what
follows.** -/
theorem cancellation_visible :
    ((caller.close protocol cancelling).run 3 .start).1 = [.effect "lookup", .effect "cancelled"] :=
  rfl

private theorem caller_no_silent_step (environment : Environment String LineEvent ℕ Unit)
    (state next : Call) : (caller.close protocol environment).step state ≠ some (.silent next) := by
  cases state <;> simp [Machine.close, caller]

private theorem caller_no_silent (environment : Environment String LineEvent ℕ Unit)
    {state middle : Call}
    (administrative : Relation.ReflTransGen
      ((caller.close protocol environment).readingOutside (· = Call.start)).silent state middle) :
    middle = state := by
  induction administrative using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head silences _ _ => exact absurd silences (caller_no_silent_step environment _ _)

private theorem outside_block_iff (environment : Environment String LineEvent ℕ Unit)
    (events : List LineEvent) (state next : Call) :
    ((caller.close protocol environment).readingOutside (· = Call.start)).Block events state next ↔
      state ≠ .start ∧ (caller.close protocol environment).step state = some (.publish events next) := by
  constructor
  · rintro ⟨middle, administrative, completes, out⟩
    have same := caller_no_silent environment administrative
    subst same
    exact ⟨out, completes⟩
  · rintro ⟨out, completes⟩
    exact ⟨state, .refl, completes, out⟩

/-- **Classifying the callback as external erases its events from the blocks**:
the blocks of the reentrant and of the plain callback coincide, while their
closed traces differ. -/
theorem external_erases_callback :
    (∀ events state next,
      ((caller.close protocol reentrant).readingOutside (· = Call.start)).Block events state next ↔
        ((caller.close protocol plain).readingOutside (· = Call.start)).Block events state next) ∧
      ((caller.close protocol reentrant).run 3 .start).1 ≠ ((caller.close protocol plain).run 3 .start).1 := by
  refine ⟨fun events state next => ?_, by decide⟩
  rw [outside_block_iff, outside_block_iff]
  cases state with
  | start => simp
  | after => simp [Machine.close, caller]
  | done => simp [Machine.close, caller]

/-! ## Compiled blocks settle -/

open BlockTransportControls in
/-- The four-step lowering's administrative work is bounded by the number of
administrative steps left. -/
def fourRank : AdministrativeRank fourReading where
  rank
    | .ready => 3
    | .first => 2
    | .second => 1
    | _ => 0
  decreases := by
    rintro _ _ ⟨step, notDone⟩
    cases step with
    | opening => decide
    | sending => decide
    | receiving => decide
    | closing => exact absurd rfl notDone

open BlockTransportControls in
/-- **Every primitive prefix of the compiled exchange is a source run followed
by a bounded administrative residual.** -/
theorem four_prefix_settles {term : Phase} {target' : Lowered}
    (protocol : Relation.ReflTransGen fourReading.ProtocolStep (lowerFour term) target') :
    ∃ target, Relation.ReflTransGen exchange.Step term target ∧
      ∃ settled, lowerFour target = settled ∧
        Relation.ReflTransGen fourReading.silent settled target' ∧ fourRank.rank target' ≤ 3 := by
  obtain ⟨target, run, settled, equivalent, administrative, bound⟩ :=
    fourBlocks.prefix_settles fourRank protocol
  refine ⟨target, run, settled, equivalent, administrative, bound.trans ?_⟩
  cases settled <;> decide

/-! ## Relation-level transport -/

inductive Check where
  | start
  | verdict
  deriving DecidableEq

inductive Interpret where
  | start
  | first
  | second
  | emitted
  deriving DecidableEq

/-- A checker that accepts in one visible step. -/
def checker : Machine Check LineEvent Unit Empty where
  step
    | .start => some (.publish [.answer 1] .verdict)
    | .verdict => some (.finish ())

/-- An interpreter that takes two administrative steps first. -/
def interpreter : Machine Interpret LineEvent Unit Empty where
  step
    | .start => some (.silent .first)
    | .first => some (.silent .second)
    | .second => some (.publish [.answer 1] .emitted)
    | .emitted => some (.finish ())

/-- The checker's start is related to three interpreter states: the relation is
not a function. -/
def related : Check → Interpret → Prop
  | .start, .start => True
  | .start, .first => True
  | .start, .second => True
  | .verdict, .emitted => True
  | _, _ => False

theorem forward : CostSimulation checker interpreter related 3 where
  silent := by
    intro state state' next _ stepped
    cases state <;> simp [checker] at stepped
  publish := by
    intro state state' events next relatedStates stepped
    cases state with
    | start =>
        simp only [checker, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        cases state' with
        | start => exact ⟨3, le_rfl, .emitted, rfl, trivial⟩
        | first => exact ⟨2, by omega, .emitted, rfl, trivial⟩
        | second => exact ⟨1, by omega, .emitted, rfl, trivial⟩
        | emitted => exact relatedStates.elim
    | verdict => simp [checker] at stepped
  finish := by
    intro state state' verdict relatedStates stepped
    cases state with
    | start => simp [checker] at stepped
    | verdict =>
        cases state' <;> simp only [related] at relatedStates
        exact ⟨1, by omega, by cases verdict; rfl⟩
  fail := by
    intro state state' events _ stepped
    cases state <;> simp [checker] at stepped
  call := by
    intro state state' request saved _ stepped
    cases state <;> simp [checker] at stepped

theorem backward : CostSimulation interpreter checker (fun state' state => related state state') 1 where
  silent := by
    intro state' state next relatedStates stepped
    cases state' with
    | start =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial⟩
    | first =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial⟩
    | second => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped
  publish := by
    intro state' state events next relatedStates stepped
    cases state' with
    | second =>
        simp only [interpreter, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨1, le_rfl, .verdict, rfl, trivial⟩
    | start => simp [interpreter] at stepped
    | first => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped
  finish := by
    intro state' state verdict relatedStates stepped
    cases state' with
    | emitted =>
        cases state <;> simp only [related] at relatedStates
        exact ⟨1, le_rfl, by cases verdict; rfl⟩
    | start => simp [interpreter] at stepped
    | first => simp [interpreter] at stepped
    | second => simp [interpreter] at stepped
  fail := by
    intro state' state events _ stepped
    cases state' <;> simp [interpreter] at stepped
  call := by
    intro state' state request saved _ stepped
    cases state' <;> simp [interpreter] at stepped

/-- **Relation-level transport**: the checker and the interpreter have the same
final observation, through a relation that is not a function. -/
theorem check_interpret_final :
    checker.observe 2 .start = interpreter.observe 4 .start ∧
      checker.observe 2 .start = ⟨[.answer 1], .finished ()⟩ :=
  ⟨forward.final_eq backward (state := .start) (state' := .start) trivial
    (by simp [Machine.observe, Machine.run, checker, Outcome.status, Status.Final])
    (by simp [Machine.observe, Machine.run, interpreter, Outcome.status, Status.Final]), rfl⟩

/-- The constructed simulation transports at the same cost despite hidden effect names. -/
theorem masked_checker_interpreter_simulation :
    CostSimulation (checker.relabel maskEffect id id) (interpreter.relabel maskEffect id id) related 3 :=
  forward.relabel maskEffect id id

/-- Common observation transport also applies to different execution state carriers. -/
theorem masked_checker_interpreter_observation :
    (checker.relabel maskEffect id id).observe 2 .start =
      (interpreter.relabel maskEffect id id).observe 4 .start :=
  checker.relabel_observation_eq interpreter maskEffect id id 2 4 .start .start check_interpret_final.1

/-- An interpreter that spins silently. -/
def spinner : Machine Unit LineEvent Unit Empty where
  step _ := some (.silent ())

/-- **A spinning interpreter is simulated by no relation that relates it to the
checker's start, at any cost.** -/
theorem spinning_interpreter_not_simulated (relation : Check → Unit → Prop) (cost : ℕ)
    (start : relation .start ()) : ¬ CostSimulation checker spinner relation cost := by
  intro simulation
  obtain ⟨k, _, _, ran, _⟩ := simulation.publish start (show checker.step .start = _ from rfl)
  have spins := spinner.silent_region_incomplete (fun _ => True)
    (fun _ _ => ⟨(), rfl, trivial⟩) k () trivial
  have events := congrArg Observation.events spins
  simp only [Machine.observe, ran] at events
  cases events

/-! ## Resumable callback execution -/

/-- The callback performs an administrative advance, emits its own effect,
and replies. It is independently executable before being attached to a caller. -/
def retainedService : Machine Nat LineEvent (Reply Nat Unit) Empty where
  step
    | 0 => some (.silent 1)
    | 1 => some (.publish [.effect "reentrant"] 2)
    | _ => some (.finish (.returned 0))

def retainedCaller := caller.handle protocol retainedService (fun _ => 0)

def retainedServiceProgress : retainedService.Productive where
  rank state := if state = 0 then 1 else 0
  silent_decreases := by
    intro state next stepped
    cases state with
    | zero => simp [retainedService] at stepped; subst next; decide
    | succ state => cases state <;> simp [retainedService] at stepped
  moves state := by cases state with
    | zero => simp [retainedService]
    | succ state => cases state <;> simp [retainedService]

def retainedCallerProgress : retainedCaller.Productive :=
  Machine.Productive.handled caller protocol retainedService (fun _ => 0)
    { rank := fun _ => 0
      silent_decreases := by intro state next stepped; cases state <;> simp [caller] at stepped
      moves := by intro state; cases state <;> simp [caller] }
    retainedServiceProgress

theorem retained_handler_administration_settles (state : HandledState Call Nat String) :
    ∃ used ≤ retainedCallerProgress.rank state, ∃ settled transition,
      retainedCaller.run used state = ([], .exhausted settled) ∧
        retainedCaller.step settled = some transition ∧ transition.administrative = false :=
  retainedCallerProgress.settles state

theorem retained_service_computes_environment (request : String) :
    retainedService.run 3 0 = ((reentrant request).1, .finished (reentrant request).2) := rfl

theorem retained_callback_cost_simulation :
    CostSimulation (caller.close protocol reentrant) retainedCaller
      (fun state retained => retained = .running state) 4 :=
  caller.close_handle_costSimulation protocol (fun _ => 0) retainedService reentrant 3
    retained_service_computes_environment

theorem retained_callback_stuck_contract :
    MatchesStuck (caller.close protocol reentrant) retainedCaller
      (fun state retained => retained = .running state) 4 :=
  caller.close_handle_matchesStuck protocol (fun _ => 0) retainedService reentrant 3

theorem callback_pauses_after_effect :
    retainedCaller.run 3 (.running .start) =
      ([.effect "lookup", .effect "reentrant"], .exhausted (.handling "lookup" .after 2)) := rfl

theorem callback_retains_exact_suffix (later : Nat) :
    retainedCaller.run (3 + later) (.running .start) =
      ([.effect "lookup", .effect "reentrant"] ++
          (retainedCaller.run later (.handling "lookup" .after 2)).1,
        (retainedCaller.run later (.handling "lookup" .after 2)).2) :=
  retainedCaller.established_and_pending 3 later (.running .start) (.handling "lookup" .after 2)
    [.effect "lookup", .effect "reentrant"] callback_pauses_after_effect

/-- Resuming a service after its effect publishes only the reply and caller
answer. Restarting it would repeat the call and the effect. -/
theorem callback_resume_does_not_repeat_effect :
    retainedCaller.run 3 (.handling "lookup" .after 2) =
        ([.effect "returned", .answer 1], .finished ()) ∧
      retainedCaller.run 6 (.running .start) =
        ([.effect "lookup", .effect "reentrant", .effect "returned", .answer 1], .finished ()) :=
  ⟨rfl, rfl⟩

theorem callback_restart_repeats_effect :
    (retainedCaller.run 3 (.running .start)).1 ++ (retainedCaller.run 6 (.running .start)).1 =
      [.effect "lookup", .effect "reentrant", .effect "lookup", .effect "reentrant",
        .effect "returned", .answer 1] := rfl

theorem callback_charges_each_component :
    retainedCaller.spent (fun | .running _ => 1 | .handling _ _ _ => 0) 6 (.running .start) = 3 ∧
      retainedCaller.spent (fun | .running _ => 0 | .handling _ _ _ => 1) 6 (.running .start) = 3 ∧
      (caller.close protocol reentrant).spent (fun _ => 1) 6 .start = 3 := ⟨rfl, rfl, rfl⟩

/-- The handler can issue a further request before replying to its caller. -/
def requestingService : Machine Nat LineEvent (Reply Nat Unit) String where
  step
    | 0 => some (.publish [.effect "write"] 1)
    | 1 => some (.call "acknowledge" 2)
    | _ => some (.finish (.returned 0))

theorem nested_request_retains_both_continuations :
    (caller.handle protocol requestingService (fun _ => 0)).run 3 (.running .start) =
      ([.effect "lookup", .effect "write"], .suspended "acknowledge" (.handling "lookup" .after 2)) := rfl

theorem nested_request_does_not_fabricate_reply :
    ((caller.handle protocol requestingService (fun _ => 0)).run 100 (.running .start)).1 =
      [.effect "lookup", .effect "write"] := rfl

/-- This service waits for an acknowledgement, whose payload is not used.
The external protocol leaves its already selected return continuation intact. -/
def acknowledgementProtocol : Callback Nat LineEvent String Unit Unit where
  callEvent := .effect
  replyEvent _ := .effect "acknowledged"
  resume retained _ := retained

def acknowledgement : Environment String LineEvent Unit Unit :=
  fun _ => ([.effect "flush"], .returned ())

theorem handling_external_service_commutes :
    (caller.handle protocol requestingService (fun _ => 0)).close
        acknowledgementProtocol.throughHandler acknowledgement =
      caller.handle protocol (requestingService.close acknowledgementProtocol acknowledgement)
        (fun _ => 0) :=
  caller.handle_close protocol requestingService (fun _ => 0) acknowledgementProtocol acknowledgement

theorem nested_service_closure_preserves_effect_order :
    ((caller.handle protocol requestingService (fun _ => 0)).close
        acknowledgementProtocol.throughHandler acknowledgement).run 6 (.running .start) =
      ([.effect "lookup", .effect "write", .effect "acknowledge", .effect "flush",
        .effect "acknowledged", .effect "returned", .answer 1], .finished ()) := rfl

/-- An uncaught service fault stops the composite. A fault reply is a
different event: it returns control to the callback protocol. -/
def failingService : Machine Unit LineEvent (Reply Nat Unit) Empty where
  step _ := some (.fail [.fault ()])

def faultReplyService : Machine Unit LineEvent (Reply Nat Unit) Empty where
  step _ := some (.finish (.faulted ()))

theorem service_fault_and_fault_reply_differ :
    (caller.handle protocol failingService (fun _ => ())).run 3 (.running .start) =
        ([.effect "lookup", .fault ()], .faulted) ∧
      (caller.handle protocol faultReplyService (fun _ => ())).run 3 (.running .start) =
        ([.effect "lookup", .fault ()], .finished ()) := ⟨rfl, rfl⟩

def cancelledService : Machine Unit LineEvent (Reply Nat Unit) Empty where
  step _ := some (.finish .cancelled)

theorem cancelled_service_does_not_publish_caller_answer :
    (caller.handle protocol cancelledService (fun _ => ())).run 3 (.running .start) =
      ([.effect "lookup", .effect "cancelled"], .finished ()) := rfl

def stuckService : Machine Unit LineEvent (Reply Nat Unit) Empty where
  step _ := none

theorem stuck_service_retains_caller :
    (caller.handle protocol stuckService (fun _ => ())).run 2 (.running .start) =
      ([.effect "lookup"], .stuck (.handling "lookup" .after ())) := rfl

def spinningService : Machine Unit LineEvent (Reply Nat Unit) Empty where
  step _ := some (.silent ())

theorem spinning_service_diverges : spinningService.DivergesWithin () := by
  intro fuel
  refine ⟨(), ?_⟩
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem running_handler_can_diverge :
    (caller.handle protocol spinningService (fun _ => ())).DivergesWithin (.handling "lookup" .after ()) :=
  caller.handle_divergesWithin protocol spinningService (fun _ => ()) "lookup" .after ()
    spinning_service_diverges

/-- Terminating atomic environments cannot stand in for a spinning service. -/
theorem spinning_service_has_no_atomic_response (fuel : Nat) (events : List LineEvent)
    (reply : Reply Nat Unit) : spinningService.run fuel () ≠ (events, .finished reply) := by
  obtain ⟨residual, retained⟩ := spinning_service_diverges fuel
  intro finished
  rw [finished] at retained
  cases retained

end Mettapedia.GSLT.Distinction.ProductiveBlocks.Controls
