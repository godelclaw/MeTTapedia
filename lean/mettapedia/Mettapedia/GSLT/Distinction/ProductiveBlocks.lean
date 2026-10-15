import Mettapedia.GSLT.Distinction.BlockTransport
import Mettapedia.GSLT.Dynamics.OrderedDemand

/-!
# Productive blocks, exact residuals and relation-level transport

`BlockTransport` reads a target's primitive steps as administrative or
completing, but it does not observe administrative divergence or deadlock.
This module adds what finite fuel, suspension, cancellation and late fallback
need, for a deterministic machine whose transitions publish ordered events.

* **Machines and finite runs** (`Machine`, `Machine.run`).  A transition is
  administrative (silent), publishes events and continues, finishes with a
  verdict, fails with fault events, calls out with a saved continuation, or
  does not exist (a stuck state).  A finite run returns its published events
  and its outcome: finished, faulted, suspended (with the request and the saved
  continuation), stuck, or exhausted (with the exact residual state).  Its
  observation (`Machine.observe`) carries the explicit `OrderedDemand.Status`.
* **Exact residuals** (`Machine.run_add`, `Machine.established_and_pending`).
  Running longer is resuming the saved residual: the events already published
  stay, and the residual's own run supplies exactly the pending ones.  A
  fallback that resumes its residual never restarts; restarting re-delivers
  and re-commits (the controls).  Finite observations grow by prefixes, and a
  final status is never revised (`Machine.observe_prefix`).
* **Progress** (`Machine.Productive`, `Machine.Productive.settles`).  A rank
  that decreases on administrative steps bounds administrative work, and a
  machine without stuck states then reaches a visible transition within the
  rank.  Without such a premise nothing completes: a stuck state and a silent
  region never acquire a final status (`Machine.stuck_incomplete`,
  `Machine.silent_region_incomplete`), and a silent region admits no rank
  (`Machine.not_productive_of_silent_region`).
* **Accounts** (`Machine.spent`, `Machine.spent_add`, `Machine.spent_le`).
  Instruction and allocation accounts are separate price functions with an
  explicit pointwise bound between them; resumption adds accounts exactly.
* **Observation relabeling** (`Machine.relabel`, `Machine.run_relabel`).
  Event, verdict and request maps retain the complete execution state and
  transition kind. Finite runs, resumption, accounts and administrative ranks
  transport through these maps. Identity and composition hold exactly.
  Noninjective maps retain occurrence order and multiplicity but can erase
  label distinctions; recovering the original run requires injectivity.
* **Foreign callbacks** (`Callback`, `Machine.close`).  A call publishes its
  request event, the events of the callback's own execution (reentrant calls
  and effects included), and a visible reply event (return, fault or
  cancellation), then continues the saved owned continuation
  (`Machine.close_run_of_suspended`), and productivity survives closing
  (`Machine.Productive.closed`).  The theorems hold for callbacks of this
  shape, which report their events and reply once; they are not claimed for
  arbitrary callbacks.  Classifying a callback as external would erase its
  events from the blocks (a control).
* **Resumable callbacks** (`HandledState`, `Machine.handle`).  A callback can
  execute as another machine, retaining both continuations across budget
  exhaustion and further requests. Its faults, stuck endpoints and divergence
  remain distinct from replies. Administrative ranks compose, and bounded
  terminating services construct a cost simulation from atomic `close`.
  Closing further service requests commutes with this construction. These are
  execution laws; copying represented state does not grant effect authority.
  For the broader handler-as-computation approach, see Xia et al.,
  *Interaction Trees* (2020), sections 3.2–3.3,
  https://doi.org/10.1145/3371119. This module uses explicit machine states
  and finite budgets, not that paper's coinductive representation.
* **Blocks** (`Machine.reading`, `Machine.block_run`).  The machine's own steps
  form a GSLT with a block reading; every block is realized by the run with
  its exact events, blocks are unique (`Machine.block_unique`), and
  productivity says that administrative work between them is bounded.
* **Compiled blocks** (`CompiledBlocks.prefix_settles`).  With bounded
  administrative work, `prefixReflection` makes every primitive protocol prefix
  of a compiled program a source run followed by a bounded administrative
  residual.
* **Relation-level transport** (`CostSimulation`,
  `CostSimulation.observe_prefix`).  A relation between the actual states of two
  machines, in which every source transition is matched by at most `cost`
  target transitions publishing the same events, carrying finishing, faults and
  suspensions with related saved continuations.  The relation need not be a
  function; a source run's observation is a prefix of the target's at `cost`
  times the fuel.  With a simulation in each direction, final observations
  coincide and a source that never completes has a target that never completes
  (`CostSimulation.final_eq`, `CostSimulation.never_completes`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation)

/-- One primitive transition of a deterministic machine. -/
inductive Transition (State Event Verdict Request : Type) where
  /-- Administrative work, silent to the observer. -/
  | silent (next : State)
  /-- Publish events in order and continue. -/
  | publish (events : List Event) (next : State)
  /-- Finish with a verdict. -/
  | finish (verdict : Verdict)
  /-- Fail, publishing the fault events. -/
  | fail (events : List Event)
  /-- Call out, saving the continuation that the reply resumes. -/
  | call (request : Request) (saved : State)

namespace Transition

variable {State Event Event' Event'' Verdict Verdict' Verdict'' Request Request' Request'' : Type}

/-- Relabel the observations of a transition without changing any retained state. -/
def relabel (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    Transition State Event Verdict Request → Transition State Event' Verdict' Request'
  | .silent next => .silent next
  | .publish published next => .publish (published.map events) next
  | .finish verdict => .finish (verdicts verdict)
  | .fail faults => .fail (faults.map events)
  | .call request saved => .call (requests request) saved

theorem relabel_id (transition : Transition State Event Verdict Request) :
    transition.relabel id id id = transition := by
  cases transition <;> simp only [relabel, List.map_id, id_eq]

theorem relabel_comp (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (events' : Event' → Event'') (verdicts' : Verdict' → Verdict'') (requests' : Request' → Request'')
    (transition : Transition State Event Verdict Request) :
    (transition.relabel events verdicts requests).relabel events' verdicts' requests' =
      transition.relabel (events' ∘ events) (verdicts' ∘ verdicts) (requests' ∘ requests) := by
  cases transition <;> simp only [relabel, List.map_map, Function.comp_apply]

/-- Recovering the original labels requires injective observation maps. -/
theorem relabel_injective (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (eventsInjective : Function.Injective events) (verdictsInjective : Function.Injective verdicts)
    (requestsInjective : Function.Injective requests) :
    Function.Injective (relabel (State := State) events verdicts requests) := by
  have listsInjective := List.map_injective_iff.mpr eventsInjective
  intro first second same
  cases first <;> cases second <;>
    simp_all only [relabel, Transition.silent.injEq, Transition.publish.injEq, Transition.finish.injEq,
      Transition.fail.injEq, Transition.call.injEq, reduceCtorEq, listsInjective.eq_iff,
      verdictsInjective.eq_iff, requestsInjective.eq_iff]

end Transition

/-- Whether a transition is administrative. -/
def Transition.administrative {State Event Verdict Request : Type} :
    Transition State Event Verdict Request → Bool
  | .silent _ => true
  | _ => false

theorem Transition.relabel_administrative {State Event Event' Verdict Verdict' Request Request' : Type}
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (transition : Transition State Event Verdict Request) :
    (transition.relabel events verdicts requests).administrative = transition.administrative := by
  cases transition <;> rfl

/-- A deterministic machine; a state without a transition is stuck. -/
structure Machine (State Event Verdict Request : Type) where
  step : State → Option (Transition State Event Verdict Request)

/-- The outcome of a finite run. -/
inductive Outcome (State Verdict Request : Type) where
  | finished (verdict : Verdict)
  | faulted
  | suspended (request : Request) (saved : State)
  | stuck (state : State)
  | exhausted (residual : State)

namespace Outcome

variable {State Verdict Request : Type}

/-- Relabel finishing verdicts and requests while retaining every saved state. -/
def relabel {Verdict' Request' : Type} (verdicts : Verdict → Verdict') (requests : Request → Request') :
    Outcome State Verdict Request → Outcome State Verdict' Request'
  | .finished verdict => .finished (verdicts verdict)
  | .faulted => .faulted
  | .suspended request saved => .suspended (requests request) saved
  | .stuck saved => .stuck saved
  | .exhausted saved => .exhausted saved

theorem relabel_id (outcome : Outcome State Verdict Request) : outcome.relabel id id = outcome := by
  cases outcome <;> rfl

theorem relabel_comp {Verdict' Verdict'' Request' Request'' : Type}
    (verdicts : Verdict → Verdict') (requests : Request → Request')
    (verdicts' : Verdict' → Verdict'') (requests' : Request' → Request'') (outcome : Outcome State Verdict Request) :
    (outcome.relabel verdicts requests).relabel verdicts' requests' =
      outcome.relabel (verdicts' ∘ verdicts) (requests' ∘ requests) := by
  cases outcome <;> rfl

theorem relabel_injective {Verdict' Request' : Type} (verdicts : Verdict → Verdict') (requests : Request → Request')
    (verdictsInjective : Function.Injective verdicts) (requestsInjective : Function.Injective requests) :
    Function.Injective (relabel (State := State) verdicts requests) := by
  intro first second same
  cases first <;> cases second <;>
    simp_all only [relabel, Outcome.finished.injEq, Outcome.suspended.injEq,
      Outcome.stuck.injEq, Outcome.exhausted.injEq, reduceCtorEq,
      verdictsInjective.eq_iff, requestsInjective.eq_iff]

/-- The observed status: stuck and exhausted runs are incomplete. -/
def status : Outcome State Verdict Request → Status Verdict
  | .finished verdict => .finished verdict
  | .faulted => .faulted
  | .suspended _ _ => .suspended
  | .stuck _ => .incomplete
  | .exhausted _ => .incomplete

/-- Relabeling never turns incompleteness into completion or reverses it. -/
theorem relabel_final_iff {Verdict' Request' : Type} (verdicts : Verdict → Verdict') (requests : Request → Request')
    (outcome : Outcome State Verdict Request) :
    (outcome.relabel verdicts requests).status.Final ↔ outcome.status.Final := by
  cases outcome <;> rfl

theorem relabel_exhausted_iff {Verdict' Request' : Type}
    (verdicts : Verdict → Verdict') (requests : Request → Request')
    (outcome : Outcome State Verdict Request) (residual : State) :
    outcome.relabel verdicts requests = .exhausted residual ↔ outcome = .exhausted residual := by
  cases outcome <;> simp only [relabel, Outcome.exhausted.injEq, reduceCtorEq]

/-- Equal statuses remain equal after relabeling, regardless of retained state types. -/
theorem relabel_status_eq {State' Verdict' Request' : Type}
    (verdicts : Verdict → Verdict') (requests : Request → Request')
    (first : Outcome State Verdict Request) (second : Outcome State' Verdict Request)
    (same : first.status = second.status) :
    (first.relabel verdicts requests).status = (second.relabel verdicts requests).status := by
  cases first <;> cases second <;> simp_all only [relabel, status, Status.finished.injEq, reduceCtorEq]

end Outcome

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- Relabel event, verdict and request carriers without changing execution state. -/
def relabel {Event' Verdict' Request' : Type} (events : Event → Event') (verdicts : Verdict → Verdict')
    (requests : Request → Request') : Machine State Event' Verdict' Request' where
  step state := (machine.step state).map (Transition.relabel events verdicts requests)

theorem relabel_id : machine.relabel id id id = machine := by
  cases machine with
  | mk step =>
      apply congrArg (fun following => (⟨following⟩ : Machine State Event Verdict Request))
      funext state
      cases found : step state <;>
        simp only [found, Option.map_none, Option.map_some, Transition.relabel_id]

theorem relabel_comp {Event' Event'' Verdict' Verdict'' Request' Request'' : Type}
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (events' : Event' → Event'') (verdicts' : Verdict' → Verdict'') (requests' : Request' → Request'') :
    (machine.relabel events verdicts requests).relabel events' verdicts' requests' =
      machine.relabel (events' ∘ events) (verdicts' ∘ verdicts) (requests' ∘ requests) := by
  apply congrArg (fun following => (⟨following⟩ : Machine State Event'' Verdict'' Request''))
  funext state
  cases found : machine.step state <;>
    simp only [relabel, found, Option.map_none, Option.map_some, Transition.relabel_comp]

theorem relabel_step {Event' Verdict' Request' : Type} (events : Event → Event') (verdicts : Verdict → Verdict')
    (requests : Request → Request') (state : State) (transition : Transition State Event Verdict Request)
    (stepped : machine.step state = some transition) :
    (machine.relabel events verdicts requests).step state = some (transition.relabel events verdicts requests) := by
  simp only [relabel, stepped, Option.map_some]

theorem relabel_step_iff {Event' Verdict' Request' : Type} (events : Event → Event') (verdicts : Verdict → Verdict')
    (requests : Request → Request') (state : State) (transition : Transition State Event' Verdict' Request') :
    (machine.relabel events verdicts requests).step state = some transition ↔
      ∃ original, machine.step state = some original ∧ original.relabel events verdicts requests = transition :=
  Option.map_eq_some_iff

/-- A finite run: the events it published and its outcome. -/
def run : ℕ → State → List Event × Outcome State Verdict Request
  | 0, state => ([], .exhausted state)
  | fuel + 1, state =>
      match machine.step state with
      | none => ([], .stuck state)
      | some (.silent next) => run fuel next
      | some (.publish events next) =>
          (events ++ (run fuel next).1, (run fuel next).2)
      | some (.finish verdict) => ([], .finished verdict)
      | some (.fail events) => (events, .faulted)
      | some (.call request saved) => ([], .suspended request saved)

theorem run_succ_stuck {fuel : ℕ} {state : State} (stepped : machine.step state = none) :
    machine.run (fuel + 1) state = ([], .stuck state) := by
  simp only [run, stepped]

theorem run_succ_silent {fuel : ℕ} {state next : State}
    (stepped : machine.step state = some (.silent next)) :
    machine.run (fuel + 1) state = machine.run fuel next := by
  simp only [run, stepped]

theorem run_succ_publish {fuel : ℕ} {state next : State} {events : List Event}
    (stepped : machine.step state = some (.publish events next)) :
    machine.run (fuel + 1) state = (events ++ (machine.run fuel next).1, (machine.run fuel next).2) := by
  simp only [run, stepped]

theorem run_succ_finish {fuel : ℕ} {state : State} {verdict : Verdict}
    (stepped : machine.step state = some (.finish verdict)) :
    machine.run (fuel + 1) state = ([], .finished verdict) := by
  simp only [run, stepped]

theorem run_succ_fail {fuel : ℕ} {state : State} {events : List Event}
    (stepped : machine.step state = some (.fail events)) :
    machine.run (fuel + 1) state = (events, .faulted) := by
  simp only [run, stepped]

theorem run_succ_call {fuel : ℕ} {state saved : State} {request : Request}
    (stepped : machine.step state = some (.call request saved)) :
    machine.run (fuel + 1) state = ([], .suspended request saved) := by
  simp only [run, stepped]

/-- Reaching a stuck outcome exposes the exact trace and residual immediately
before the unsuccessful transition lookup. -/
theorem run_stuck_prefix {fuel : Nat} {state stopped : State} {events : List Event}
    (ran : machine.run fuel state = (events, .stuck stopped)) :
    ∃ count < fuel, machine.run count state = (events, .exhausted stopped) ∧
      machine.step stopped = none := by
  induction fuel generalizing state events with
  | zero => simp only [run, Prod.mk.injEq, reduceCtorEq, and_false] at ran
  | succ fuel ih =>
      cases found : machine.step state with
      | none =>
          simp only [run, found, Prod.mk.injEq, Outcome.stuck.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          exact ⟨0, Nat.zero_lt_succ _, rfl, found⟩
      | some transition =>
          cases transition with
          | silent next =>
              rw [machine.run_succ_silent found] at ran
              obtain ⟨count, bound, paused, blocked⟩ := ih ran
              exact ⟨count + 1, Nat.succ_lt_succ bound,
                (machine.run_succ_silent found).trans paused, blocked⟩
          | publish published next =>
              rw [machine.run_succ_publish found] at ran
              have same := Prod.mk.inj ran
              have later : machine.run fuel next =
                  ((machine.run fuel next).1, .stuck stopped) := Prod.ext rfl same.2
              obtain ⟨count, bound, paused, blocked⟩ := ih later
              refine ⟨count + 1, Nat.succ_lt_succ bound, ?_, blocked⟩
              rw [machine.run_succ_publish found, paused]
              exact Prod.ext same.1 rfl
          | finish verdict => simp only [run, found, Prod.mk.injEq, reduceCtorEq, and_false] at ran
          | fail faults => simp only [run, found, Prod.mk.injEq, reduceCtorEq, and_false] at ran
          | call request saved => simp only [run, found, Prod.mk.injEq, reduceCtorEq, and_false] at ran

/-- Total transition classification excludes stuck outcomes, independently of
termination and independently of any administrative rank. -/
theorem run_not_stuck_of_moves (moves : ∀ state, machine.step state ≠ none)
    (fuel : Nat) (state stopped : State) : (machine.run fuel state).2 ≠ .stuck stopped := by
  intro impossible
  obtain ⟨_, _, _, blocked⟩ := machine.run_stuck_prefix (Prod.ext rfl impossible)
  exact moves stopped blocked

/-- The observation of a finite run. -/
def observe (fuel : ℕ) (state : State) : Observation Event Verdict :=
  ⟨(machine.run fuel state).1, (machine.run fuel state).2.status⟩

/-- Continue a finite run from its exhausted residual; every other outcome
already ends the run. -/
def continueRun (second : ℕ) :
    List Event × Outcome State Verdict Request → List Event × Outcome State Verdict Request
  | (events, .exhausted residual) =>
      (events ++ (machine.run second residual).1, (machine.run second residual).2)
  | result => result

theorem continueRun_prepend (second : ℕ) (events : List Event)
    (result : List Event × Outcome State Verdict Request) :
    machine.continueRun second (events ++ result.1, result.2) =
      (events ++ (machine.continueRun second result).1, (machine.continueRun second result).2) := by
  rcases result with ⟨published, outcome⟩
  cases outcome <;> simp [continueRun, List.append_assoc]

/-- **Exact residuals: running longer is resuming the saved residual.** -/
theorem run_add (first second : ℕ) (state : State) :
    machine.run (first + second) state = machine.continueRun second (machine.run first state) := by
  induction first generalizing state with
  | zero => simp [run, continueRun]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases found : machine.step state with
      | none => simp [run, found, continueRun]
      | some transition =>
          cases transition with
          | silent next => simp only [run, found, ih next]
          | publish events next =>
              simp only [run, found, ih next]
              exact (machine.continueRun_prepend second events (machine.run first next)).symm
          | finish verdict => simp [run, found, continueRun]
          | fail events => simp [run, found, continueRun]
          | call request saved => simp [run, found, continueRun]

/-- **A finite prefix keeps its established events, and its residual keeps
exactly the pending ones.** -/
theorem established_and_pending (first second : ℕ) (state residual : State)
    (events : List Event) (paused : machine.run first state = (events, .exhausted residual)) :
    machine.run (first + second) state =
      (events ++ (machine.run second residual).1, (machine.run second residual).2) := by
  rw [run_add, paused]
  rfl

/-- A run that did not exhaust its fuel is not changed by more fuel. -/
theorem run_stable (first second : ℕ) (state : State)
    (ended : ∀ residual, (machine.run first state).2 ≠ .exhausted residual) :
    machine.run (first + second) state = machine.run first state := by
  rw [run_add]
  rcases outcome : machine.run first state with ⟨events, result⟩
  rw [outcome] at ended
  cases result with
  | exhausted residual => exact absurd rfl (ended residual)
  | _ => rfl

/-- Execution keeps advancing for every finite budget before a request,
termination, fault or stuck boundary. This includes silent and reactive
divergence; a separate observer distinguishes their event streams. -/
def DivergesWithin (state : State) : Prop :=
  ∀ fuel, ∃ residual, (machine.run fuel state).2 = .exhausted residual

theorem DivergesWithin.not_stuck {state : State} (diverges : machine.DivergesWithin state)
    (fuel : Nat) (stopped : State) : (machine.run fuel state).2 ≠ .stuck stopped := by
  obtain ⟨residual, remains⟩ := diverges fuel
  rw [remains]
  intro impossible
  cases impossible

theorem not_divergesWithin_of_stuck {state : State} (blocked : machine.step state = none) :
    ¬ machine.DivergesWithin state := by
  intro diverges
  exact diverges.not_stuck machine 1 state
    (congrArg Prod.snd (machine.run_succ_stuck (fuel := 0) blocked))

/-- Continuing the complete saved residual preserves divergence inside the
current interaction region. -/
theorem DivergesWithin.resume {state residual : State} {fuel : Nat} {events : List Event}
    (diverges : machine.DivergesWithin state)
    (paused : machine.run fuel state = (events, .exhausted residual)) :
    machine.DivergesWithin residual := by
  intro later
  obtain ⟨residual', remains⟩ := diverges (fuel + later)
  rw [machine.established_and_pending fuel later state residual events paused] at remains
  exact ⟨residual', remains⟩

/-- **Finite observations grow by prefixes; a final status is never revised.** -/
theorem observe_prefix (first second : ℕ) (state : State) :
    (machine.observe first state).Prefix (machine.observe (first + second) state) := by
  simp only [observe, run_add]
  rcases machine.run first state with ⟨events, result⟩
  cases result with
  | exhausted residual =>
      exact ⟨List.prefix_append _ _, fun final => final.elim⟩
  | _ => exact Observation.Prefix.refl _

theorem observe_prefix_of_le {first second : ℕ} (le : first ≤ second) (state : State) :
    (machine.observe first state).Prefix (machine.observe second state) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact machine.observe_prefix first extra state

/-! ## Progress -/

/-- **A productive machine**: administrative work is bounded by a rank that
every administrative step decreases, and no state is stuck. -/
structure Productive where
  rank : State → ℕ
  silent_decreases : ∀ {state next : State}, machine.step state = some (.silent next) →
    rank next < rank state
  moves : ∀ state, machine.step state ≠ none

/-- **Administrative work ends within the rank** at a visible transition. -/
theorem Productive.settles {machine : Machine State Event Verdict Request}
    (productive : machine.Productive) (state : State) :
    ∃ k ≤ productive.rank state, ∃ settled transition,
      machine.run k state = ([], .exhausted settled) ∧ machine.step settled = some transition ∧
        transition.administrative = false := by
  induction h : productive.rank state using Nat.strong_induction_on generalizing state with
  | _ n ih =>
      cases found : machine.step state with
      | none => exact absurd found (productive.moves state)
      | some transition =>
          cases administrative : transition.administrative with
          | false => exact ⟨0, Nat.zero_le _, state, transition, rfl, found, administrative⟩
          | true =>
              cases transition with
              | silent next =>
                  have smaller := productive.silent_decreases found
                  obtain ⟨k, bound, settled, final, ran, stepped, visible⟩ :=
                    ih (productive.rank next) (h ▸ smaller) next rfl
                  refine ⟨k + 1, by omega, settled, final, ?_, stepped, visible⟩
                  simp only [run, found, ran]
              | _ => simp [Transition.administrative] at administrative

/-- **A stuck state never acquires completion.** -/
theorem stuck_incomplete (state : State) (stuck : machine.step state = none) (fuel : ℕ) :
    machine.observe fuel state = ⟨[], .incomplete⟩ := by
  cases fuel <;> simp [observe, run, stuck, Outcome.status]

/-- **A silent region never acquires completion**: states that only step
silently to states of the region publish nothing and stay incomplete. -/
theorem silent_region_incomplete (region : State → Prop)
    (closed : ∀ state, region state → ∃ next, machine.step state = some (.silent next) ∧ region next)
    (fuel : ℕ) (state : State) (inside : region state) :
    machine.observe fuel state = ⟨[], .incomplete⟩ := by
  induction fuel generalizing state with
  | zero => simp [observe, run, Outcome.status]
  | succ fuel ih =>
      obtain ⟨next, stepped, nextInside⟩ := closed state inside
      have later := ih next nextInside
      simp only [observe] at later ⊢
      simpa only [run, stepped] using later

/-- A silent region admits no rank: such a machine is not productive. -/
theorem not_productive_of_silent_region (region : State → Prop)
    (closed : ∀ state, region state → ∃ next, machine.step state = some (.silent next) ∧ region next)
    (state : State) (inside : region state) : IsEmpty machine.Productive := by
  refine ⟨fun productive => ?_⟩
  have descent : ∀ n, ∀ state, productive.rank state = n → ¬ region state := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro state ranked inRegion
        obtain ⟨next, stepped, nextInside⟩ := closed state inRegion
        exact ih _ (ranked ▸ productive.silent_decreases stepped) next rfl nextInside
  exact descent _ state rfl inside

/-! ## Accounts -/

/-- The account of a finite run under a price for each transition taken. -/
def spent (price : State → ℕ) : ℕ → State → ℕ
  | 0, _ => 0
  | fuel + 1, state =>
      match machine.step state with
      | none => 0
      | some (.silent next) => price state + spent price fuel next
      | some (.publish _ next) => price state + spent price fuel next
      | some _ => price state

/-- The account still to be charged from a finite run's outcome. -/
def spentAfter (price : State → ℕ) (second : ℕ) : Outcome State Verdict Request → ℕ
  | .exhausted residual => machine.spent price second residual
  | _ => 0

/-- **Resumption adds accounts exactly.** -/
theorem spent_add (price : State → ℕ) (first second : ℕ) (state : State) :
    machine.spent price (first + second) state =
      machine.spent price first state + machine.spentAfter price second (machine.run first state).2 := by
  induction first generalizing state with
  | zero => simp [spent, run, spentAfter]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases found : machine.step state with
      | none => simp [spent, run, found, spentAfter]
      | some transition =>
          cases transition with
          | silent next => simp only [spent, run, found, ih next, Nat.add_assoc]
          | publish events next => simp only [spent, run, found, ih next, Nat.add_assoc]
          | finish verdict => simp [spent, run, found, spentAfter]
          | fail events => simp [spent, run, found, spentAfter]
          | call request saved => simp [spent, run, found, spentAfter]

/-- **An explicit pointwise bound between two accounts bounds their totals.** -/
theorem spent_le (instructions allocations : State → ℕ) (factor : ℕ)
    (bound : ∀ state, allocations state ≤ factor * instructions state) (fuel : ℕ) (state : State) :
    machine.spent allocations fuel state ≤ factor * machine.spent instructions fuel state := by
  induction fuel generalizing state with
  | zero => simp [spent]
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp [spent, found]
      | some transition =>
          cases transition with
          | silent next =>
              simp only [spent, found, Nat.mul_add]
              exact Nat.add_le_add (bound state) (ih next)
          | publish events next =>
              simp only [spent, found, Nat.mul_add]
              exact Nat.add_le_add (bound state) (ih next)
          | finish verdict => simpa [spent, found] using bound state
          | fail events => simpa [spent, found] using bound state
          | call request saved => simpa [spent, found] using bound state

/-- An explicit-output account charges for every published event, including
batched publications and fault events. Its output-size lower bound holds
independently of a regional machine's internal scheduling. -/
theorem output_length_le_spent (price : State → Nat)
    (publishes : ∀ state events next, machine.step state = some (.publish events next) →
      events.length ≤ price state)
    (fails : ∀ state events, machine.step state = some (.fail events) →
      events.length ≤ price state)
    (fuel : Nat) (state : State) :
    (machine.run fuel state).1.length ≤ machine.spent price fuel state := by
  induction fuel generalizing state with
  | zero => simp [Machine.run, Machine.spent]
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp [Machine.run, Machine.spent, found]
      | some transition =>
          cases transition with
          | silent next =>
              simp only [Machine.run, Machine.spent, found]
              have bound := ih next
              omega
          | publish events next =>
              simpa only [Machine.run, Machine.spent, found, List.length_append] using
                Nat.add_le_add (publishes state events next found) (ih next)
          | fail events =>
              simpa only [Machine.run, Machine.spent, found] using fails state events found
          | finish verdict => simp [Machine.run, Machine.spent, found]
          | call request saved => simp [Machine.run, Machine.spent, found]

private def underpricedOutput : Machine Unit Nat Unit Empty where
  step _ := some (.publish [0, 1] ())

/-- Counting one transition as zero work cannot justify an explicit-output
lower bound: this publication delivers two answers. -/
theorem underpriced_output_breaks_lower_bound :
    (underpricedOutput.run 1 ()).1.length > underpricedOutput.spent (fun _ => 0) 1 () := by decide

/-! ## Observation relabeling -/

variable {Event' Verdict' Request' : Type}

/-- Every run has the relabeled events and outcome, with unchanged residuals. -/
theorem run_relabel (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (fuel : ℕ) (state : State) :
    (machine.relabel events verdicts requests).run fuel state =
      ((machine.run fuel state).1.map events, (machine.run fuel state).2.relabel verdicts requests) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : machine.step state with
      | none =>
          have stopped : (machine.relabel events verdicts requests).step state = none := by
            simp only [relabel, found, Option.map_none]
          simp only [run, found, stopped, List.map_nil, Outcome.relabel]
      | some transition =>
          have mapped := machine.relabel_step events verdicts requests state transition found
          cases transition <;> simp only [run, found, mapped,
            Transition.relabel, ih, List.map_append, List.map_nil, Outcome.relabel]

/-- Relabeling does not change whether execution continues for every finite
budget. It can still lose distinctions between the events of such a run. -/
theorem relabel_divergesWithin_iff (events : Event → Event') (verdicts : Verdict → Verdict')
    (requests : Request → Request') (state : State) :
    (machine.relabel events verdicts requests).DivergesWithin state ↔
      machine.DivergesWithin state := by
  simp only [DivergesWithin, run_relabel, Outcome.relabel_exhausted_iff]

/-- Observation relabeling changes no transition charge. -/
theorem spent_relabel (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (price : State → ℕ) (fuel : ℕ) (state : State) :
    (machine.relabel events verdicts requests).spent price fuel state = machine.spent price fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : machine.step state with
      | none =>
          have stopped : (machine.relabel events verdicts requests).step state = none := by
            simp only [relabel, found, Option.map_none]
          simp only [spent, found, stopped]
      | some transition =>
          have mapped := machine.relabel_step events verdicts requests state transition found
          cases transition <;> simp only [spent, found, mapped, Transition.relabel, ih]

theorem continueRun_relabel (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (fuel : ℕ) (published : List Event) (outcome : Outcome State Verdict Request) :
    (machine.relabel events verdicts requests).continueRun fuel
        (published.map events, outcome.relabel verdicts requests) =
      ((machine.continueRun fuel (published, outcome)).1.map events,
        (machine.continueRun fuel (published, outcome)).2.relabel verdicts requests) := by
  cases outcome <;> simp only [continueRun, Outcome.relabel, run_relabel, List.map_append]

/-- Completion classification survives even a noninjective observation map. -/
theorem relabel_final_iff (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (fuel : ℕ) (state : State) :
    ((machine.relabel events verdicts requests).observe fuel state).status.Final ↔
      (machine.observe fuel state).status.Final := by
  simp only [observe, run_relabel, Outcome.relabel_final_iff]

/-- Observation equality transports across machines with different state carriers. -/
theorem relabel_observation_eq {Target : Type} (target : Machine Target Event Verdict Request)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (fuel fuel' : ℕ) (state : State) (state' : Target)
    (same : machine.observe fuel state = target.observe fuel' state') :
    (machine.relabel events verdicts requests).observe fuel state =
      (target.relabel events verdicts requests).observe fuel' state' := by
  have eventsEq := congrArg Observation.events same
  have statusEq := congrArg Observation.status same
  simp only [observe] at eventsEq statusEq
  simp only [observe, run_relabel]
  exact congrArg₂ Observation.mk (congrArg (List.map events) eventsEq)
    (Outcome.relabel_status_eq verdicts requests _ _ statusEq)

/-- A represented pause has exactly the original residual, even when labels are lost. -/
theorem relabel_pause_iff (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (fuel : ℕ) (state saved : State) (published : List Event') :
    (machine.relabel events verdicts requests).run fuel state = (published, .exhausted saved) ↔
      ∃ original, machine.run fuel state = (original, .exhausted saved) ∧ original.map events = published := by
  rw [run_relabel]
  cases machine.run fuel state with
  | mk original outcome =>
      cases outcome <;> simp [Outcome.relabel, and_comm]

/-- Resumption keeps the complete original residual and the mapped occurrence prefix. -/
theorem relabel_resumed (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (first second : ℕ) (state saved : State) (published : List Event)
    (paused : machine.run first state = (published, .exhausted saved)) :
    (machine.relabel events verdicts requests).run (first + second) state =
      (published.map events ++ ((machine.relabel events verdicts requests).run second saved).1,
        ((machine.relabel events verdicts requests).run second saved).2) := by
  apply (machine.relabel events verdicts requests).established_and_pending first second state saved (published.map events)
  simp only [run_relabel, paused, Outcome.relabel]

theorem relabel_resumed_accounts (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (price : State → ℕ) (first second : ℕ) (state saved : State) (published : List Event)
    (paused : machine.run first state = (published, .exhausted saved)) :
    (machine.relabel events verdicts requests).spent price (first + second) state =
      machine.spent price first state + (machine.relabel events verdicts requests).spent price second saved := by
  rw [machine.spent_relabel, machine.spent_relabel, machine.spent_add, paused]
  rfl

/-- Equality of mapped runs reflects original equality only for injective maps. -/
theorem relabel_runs_eq_iff (other : Machine State Event Verdict Request)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (eventsInjective : Function.Injective events) (verdictsInjective : Function.Injective verdicts)
    (requestsInjective : Function.Injective requests)
    (fuel fuel' : ℕ) (state state' : State) :
    (machine.relabel events verdicts requests).run fuel state =
        (other.relabel events verdicts requests).run fuel' state' ↔
      machine.run fuel state = other.run fuel' state' := by
  have listsInjective := List.map_injective_iff.mpr eventsInjective
  have outcomesInjective := Outcome.relabel_injective (State := State) verdicts requests verdictsInjective requestsInjective
  simp only [run_relabel, Prod.mk.injEq, listsInjective.eq_iff, outcomesInjective.eq_iff]
  exact Prod.ext_iff.symm

/-- Relabeling observations preserves the same administrative rank. -/
def Productive.relabeled {machine : Machine State Event Verdict Request} (productive : machine.Productive)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    (machine.relabel events verdicts requests).Productive where
  rank := productive.rank
  moves state := by
    cases found : machine.step state with
    | none => exact False.elim (productive.moves state found)
    | some transition => simp only [relabel, found, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]
  silent_decreases := by
    intro state next stepped
    cases found : machine.step state with
    | none => simp only [relabel, found, Option.map_none] at stepped; cases stepped
    | some transition =>
        simp only [relabel, found, Option.map_some] at stepped
        cases transition with
        | silent following =>
            have same : following = next := by
              simpa only [Transition.relabel, Option.some.injEq, Transition.silent.injEq] using stepped
            rw [← same]
            exact productive.silent_decreases found
        | publish published following | finish verdict | fail faults | call request saved => cases stepped

/-- An administrative rank on relabeled execution also ranks the original machine. -/
def Productive.ofRelabeled (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request')
    (productive : (machine.relabel events verdicts requests).Productive) : machine.Productive where
  rank := productive.rank
  moves state := by
    intro stopped
    apply productive.moves state
    simp only [relabel, stopped, Option.map_none]
  silent_decreases := by
    intro state next stepped
    apply productive.silent_decreases
    exact machine.relabel_step events verdicts requests state (.silent next) stepped

/-! ## Foreign callbacks -/

end Machine

/-- A callback's visible reply. -/
inductive Reply (Value Failure : Type) where
  | returned (value : Value)
  | faulted (failure : Failure)
  | cancelled

/-- **The callback protocol**: a visible call event, a visible reply event, and
the resumption of the saved owned continuation by the reply. -/
structure Callback (State Event Request Value Failure : Type) where
  callEvent : Request → Event
  replyEvent : Reply Value Failure → Event
  resume : State → Reply Value Failure → State

/-- An environment answers a call with the events of its own execution,
reentrant calls and effects included, and one reply. -/
abbrev Environment (Request Event Value Failure : Type) :=
  Request → List Event × Reply Value Failure

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)
variable {Value Failure : Type}

/-- The events a call publishes under the protocol. -/
def callEvents (callback : Callback State Event Request Value Failure)
    (environment : Environment Request Event Value Failure) (request : Request) : List Event :=
  callback.callEvent request :: (environment request).1 ++ [callback.replyEvent (environment request).2]

/-- **Close a machine under a callback protocol and an environment**: every
call publishes its call, callback and reply events and resumes the saved
continuation. -/
def close (callback : Callback State Event Request Value Failure)
    (environment : Environment Request Event Value Failure) : Machine State Event Verdict Empty where
  step state := (machine.step state).map fun
    | .silent next => .silent next
    | .publish events next => .publish events next
    | .finish verdict => .finish verdict
    | .fail events => .fail events
    | .call request saved =>
        .publish (callEvents callback environment request)
          (callback.resume saved (environment request).2)

variable (callback : Callback State Event Request Value Failure)
  (environment : Environment Request Event Value Failure)

/-- A run that has not crossed a request boundary executes unchanged under
the callback closure. Its complete terminal or residual outcome is retained. -/
theorem close_run_of_no_request (fuel : Nat) (state : State) (events : List Event)
    (outcome : Outcome State Verdict Empty)
    (ran : machine.run fuel state = (events, outcome.relabel id Empty.elim)) :
    (machine.close callback environment).run fuel state = (events, outcome) := by
  induction fuel generalizing state events outcome with
  | zero =>
      cases outcome <;> simp_all [run, Outcome.relabel]
  | succ fuel ih =>
      cases found : machine.step state with
      | none =>
          cases outcome <;> simp_all [run, close, Outcome.relabel]
      | some transition =>
          cases transition with
          | silent next =>
              rw [machine.run_succ_silent found] at ran
              simpa only [run, close, found, Option.map_some] using ih next events outcome ran
          | publish published next =>
              rw [machine.run_succ_publish found] at ran
              have same := Prod.mk.inj ran
              have child : machine.run fuel next =
                  ((machine.run fuel next).1, outcome.relabel id Empty.elim) :=
                Prod.ext rfl same.2
              have resumed := ih next (machine.run fuel next).1 outcome child
              have closed : (machine.close callback environment).step state =
                  some (.publish published next) := by simp only [close, found, Option.map_some]
              rw [(machine.close callback environment).run_succ_publish closed, resumed]
              exact Prod.ext same.1 rfl
          | finish verdict =>
              cases outcome <;> simp_all [run, close, Outcome.relabel]
          | fail faults =>
              cases outcome <;> simp_all [run, close, Outcome.relabel]
          | call request saved =>
              cases outcome with
              | suspended impossible _ => exact impossible.elim
              | _ => simp [run, found, Outcome.relabel] at ran


/-- **A suspended run, closed under the protocol, publishes the call, the
callback's own events and the reply, then continues from the resumed saved
continuation.** -/
theorem close_run_of_suspended (fuel : ℕ) (state : State) (events : List Event)
    (request : Request) (saved : State)
    (suspended : machine.run fuel state = (events, .suspended request saved)) :
    ∃ k ≤ fuel, (machine.close callback environment).run k state =
      (events ++ callEvents callback environment request,
        .exhausted (callback.resume saved (environment request).2)) := by
  induction fuel generalizing state events with
  | zero => simp [run] at suspended
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp [run, found] at suspended
      | some transition =>
          cases transition with
          | silent next =>
              simp only [run, found] at suspended
              obtain ⟨k, bound, ran⟩ := ih next events suspended
              refine ⟨k + 1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state = some (.silent next) := by
                simp [Machine.close, found]
              simp only [run, closed, ran]
          | publish published next =>
              simp only [run, found, Prod.mk.injEq] at suspended
              obtain ⟨eventsEq, outcomeEq⟩ := suspended
              obtain ⟨k, bound, ran⟩ := ih next (machine.run fuel next).1
                (Prod.ext rfl outcomeEq)
              refine ⟨k + 1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state =
                  some (.publish published next) := by
                simp [Machine.close, found]
              simp only [run, closed, ran, ← eventsEq, List.append_assoc]
          | finish verdict => simp [run, found] at suspended
          | fail failed => simp [run, found] at suspended
          | call called savedHere =>
              simp only [run, found, Prod.mk.injEq, Outcome.suspended.injEq] at suspended
              obtain ⟨rfl, rfl, rfl⟩ := suspended
              refine ⟨1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state =
                  some (.publish (callEvents callback environment called)
                    (callback.resume savedHere (environment called).2)) := by
                simp [Machine.close, found]
              simp [run, closed]

/-- A productive machine stays productive when closed under any callback of the
protocol: a call becomes a visible transition. -/
def Productive.closed {machine : Machine State Event Verdict Request}
    (productive : machine.Productive) : (machine.close callback environment).Productive where
  rank := productive.rank
  silent_decreases := by
    intro state next stepped
    cases found : machine.step state with
    | none => simp [Machine.close, found] at stepped
    | some transition =>
        cases transition <;> simp [Machine.close, found] at stepped
        subst stepped
        exact productive.silent_decreases found
  moves state := by
    have moving := productive.moves state
    simpa [Machine.close] using moving

/-! ## The block reading of a machine -/

/-- The machine's own steps, read as a GSLT with equality as its equations. -/
abbrev gslt : GSLT.{0} where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites state next := machine.step state = some (.silent next) ∨
    ∃ events, machine.step state = some (.publish events next)
  rewrites_resp_left := by
    intro _ _ target equal stepped
    exact ⟨target, equal ▸ stepped, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ stepped equal
    exact equal ▸ stepped

/-- **The block reading**: administrative steps are silent, and a publishing
step completes a block labelled by its events. -/
def reading : BlockReading machine.gslt (List Event) where
  silent state next := machine.step state = some (.silent next)
  complete events state next := machine.step state = some (.publish events next)
  external _ _ := False
  silent_step := Or.inl
  complete_step := fun completes => Or.inr ⟨_, completes⟩
  external_step := fun never => never.elim
  classify := by
    rintro _ _ (silences | ⟨events, completes⟩)
    · exact Or.inl silences
    · exact Or.inr (Or.inl ⟨events, completes⟩)
  silent_resp_left := by
    intro _ _ next equal silences
    exact ⟨next, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ next equal completes
    exact ⟨next, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- Administrative steps are realized by the run without output. -/
theorem silent_run {state middle : State}
    (administrative : Relation.ReflTransGen machine.reading.silent state middle) :
    ∃ k, ∀ fuel, machine.run (k + fuel) state = machine.run fuel middle := by
  induction administrative using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun fuel => by simp⟩
  | head silences _ ih =>
      obtain ⟨k, ran⟩ := ih
      refine ⟨k + 1, fun fuel => ?_⟩
      rw [show k + 1 + fuel = (k + fuel) + 1 by omega]
      simp only [run]
      rw [show machine.step _ = _ from silences]
      exact ran fuel

/-- **Every block is realized by the run**, with its exact events. -/
theorem block_run {events : List Event} {state next : State}
    (block : machine.reading.Block events state next) :
    ∃ k, ∀ fuel, machine.run (k + 1 + fuel) state =
      (events ++ (machine.run fuel next).1, (machine.run fuel next).2) := by
  obtain ⟨middle, administrative, completes⟩ := block
  obtain ⟨k, ran⟩ := machine.silent_run administrative
  refine ⟨k, fun fuel => ?_⟩
  rw [show k + 1 + fuel = k + (fuel + 1) by omega, ran]
  simp only [run]
  rw [show machine.step middle = _ from completes]

/-- A block reading that classifies the publishing steps of the states in
`outside` as external interactions.  Their events then belong to no block:
the classification limits a theorem's scope, and the controls show that it
erases a callback's events from the block observations. -/
def readingOutside (outside : State → Prop) : BlockReading machine.gslt (List Event) where
  silent state next := machine.step state = some (.silent next)
  complete events state next := machine.step state = some (.publish events next) ∧ ¬ outside state
  external state next := (∃ events, machine.step state = some (.publish events next)) ∧ outside state
  silent_step := Or.inl
  complete_step := fun completes => Or.inr ⟨_, completes.1⟩
  external_step := fun interaction => Or.inr interaction.1
  classify := by
    rintro state _ (silences | ⟨events, completes⟩)
    · exact Or.inl silences
    · by_cases out : outside state
      · exact Or.inr (Or.inr ⟨⟨events, completes⟩, out⟩)
      · exact Or.inr (Or.inl ⟨events, completes, out⟩)
  silent_resp_left := by
    intro _ _ next equal silences
    exact ⟨next, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ next equal completes
    exact ⟨next, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- **Blocks with the status as crisp atoms**: the labelled system of blocks,
observing at each state the status after one transition.  Under finite
branching and a positive discount its graded zero kernel is crisp
bisimilarity (`GradedSystem.logicalDistance_ofSystem_eq_zero_iff`). -/
def statusSystem : HennessyMilner.System machine.gslt where
  Atom := Status Verdict
  observes atom state := (machine.observe 1 state).status = atom
  observes_resp atom := by
    intro _ _ equal
    change _ = _ at equal
    rw [equal]
  Label := List Event
  act := machine.reading.Block
  act_resp_left := by
    intro _ _ _ target equal block
    change _ = _ at equal
    exact ⟨target, equal ▸ block, rfl⟩
  act_resp_right := by
    intro _ _ _ _ block equal
    change _ = _ at equal
    exact equal ▸ block

/-- Administrative runs of a deterministic machine that stop at states without
an administrative step stop at the same state. -/
theorem settled_unique {start first second : State}
    (left : Relation.ReflTransGen machine.reading.silent start first)
    (right : Relation.ReflTransGen machine.reading.silent start second)
    (stopFirst : ∀ next, ¬ machine.reading.silent first next)
    (stopSecond : ∀ next, ¬ machine.reading.silent second next) : first = second := by
  induction left using Relation.ReflTransGen.head_induction_on generalizing second with
  | refl =>
      cases right using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head silences _ => exact absurd silences (stopFirst _)
  | head silences rest ih =>
      cases right using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd silences (stopSecond _)
      | head silences' rest' =>
          change machine.step _ = _ at silences silences'
          rw [silences] at silences'
          cases silences'
          exact ih rest' stopSecond

/-- **Blocks of a deterministic machine are unique.** -/
theorem block_unique {first second : List Event} {state next next' : State}
    (one : machine.reading.Block first state next) (two : machine.reading.Block second state next') :
    first = second ∧ next = next' := by
  obtain ⟨middle, administrative, completes⟩ := one
  obtain ⟨middle', administrative', completes'⟩ := two
  have stops : ∀ {middle : State} {events : List Event} {after : State},
      machine.step middle = some (.publish events after) →
        ∀ next, ¬ machine.reading.silent middle next := by
    intro middle events after visible next silences
    change machine.step _ = _ at silences
    rw [visible] at silences
    cases silences
  have same := machine.settled_unique administrative administrative' (stops completes)
    (stops completes')
  subst same
  change machine.step _ = _ at completes completes'
  rw [completes] at completes'
  cases completes'
  exact ⟨rfl, rfl⟩

end Machine

/-! ## Productive compiled blocks -/

/-- **Bounded administrative work** on a block reading: a rank that every
administrative step decreases. -/
structure AdministrativeRank {T : GSLT.{0}} {Label : Type} (B : BlockReading T Label) where
  rank : T.Term → ℕ
  decreases : ∀ {term term' : T.Term}, B.silent term term' → rank term' < rank term

theorem AdministrativeRank.rank_le {T : GSLT.{0}} {Label : Type} {B : BlockReading T Label}
    (ranked : AdministrativeRank B) {term term' : T.Term}
    (administrative : Relation.ReflTransGen B.silent term term') : ranked.rank term' ≤ ranked.rank term := by
  induction administrative with
  | refl => exact le_rfl
  | tail _ last ih => exact (ranked.decreases last).le.trans ih

/-- **Every primitive protocol prefix of a compiled program is a source run
followed by a bounded administrative residual**: `prefixReflection` supplies
the source run, and the rank bounds the administrative work since its compiled
endpoint. -/
theorem _root_.Mettapedia.GSLT.Distinction.CompiledBlocks.prefix_settles {S T : GSLT.{0}}
    {B : BlockReading T Unit}
    (compiled : CompiledBlocks S T B) (ranked : AdministrativeRank B) {term : S.Term}
    {target' : T.Term}
    (protocol : Relation.ReflTransGen B.ProtocolStep (compiled.realization.mapTerm term) target') :
    ∃ target, Relation.ReflTransGen S.Step term target ∧
      ∃ settled, T.Equiv (compiled.realization.mapTerm target) settled ∧
        Relation.ReflTransGen B.silent settled target' ∧ ranked.rank target' ≤ ranked.rank settled := by
  obtain ⟨target, run, settled, equivalent, administrative⟩ := compiled.prefixReflection protocol
  exact ⟨target, run, settled, equivalent, administrative, ranked.rank_le administrative⟩

/-! ## Relation-level transport with a cost bound -/

/-- **A cost-bounded simulation between the actual states of two machines.**
Every source transition from related states is matched by at most `cost`
target transitions that publish the same events and end in related states, or
reach the same verdict, the same faults, or the same request with related
saved continuations.  The relation need not be a function. -/
structure CostSimulation {Source Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request) (target : Machine Target Event Verdict Request)
    (related : Source → Target → Prop) (cost : ℕ) : Prop where
  silent : ∀ {state state' next}, related state state' → source.step state = some (.silent next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = ([], .exhausted next') ∧ related next next'
  publish : ∀ {state state' events next}, related state state' →
    source.step state = some (.publish events next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = (events, .exhausted next') ∧ related next next'
  finish : ∀ {state state' verdict}, related state state' →
    source.step state = some (.finish verdict) →
    ∃ k ≤ cost, target.run k state' = ([], .finished verdict)
  fail : ∀ {state state' events}, related state state' → source.step state = some (.fail events) →
    ∃ k ≤ cost, target.run k state' = (events, .faulted)
  call : ∀ {state state' request saved}, related state state' →
    source.step state = some (.call request saved) →
    ∃ k ≤ cost, ∃ saved', target.run k state' = ([], .suspended request saved') ∧ related saved saved'

/-- Matching absent transitions is additional to matching existing transitions.
It retains the stuck endpoint without introducing events. The bound accounts
for the transition lookup that observes stuckness, as in `Machine.run`. -/
def MatchesStuck {Source Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request) (target : Machine Target Event Verdict Request)
    (related : Source → Target → Prop) (cost : Nat) : Prop :=
  ∀ ⦃state state'⦄, related state state' → source.step state = none →
    ∃ count ≤ cost, ∃ stopped, target.run count state' = ([], .stuck stopped) ∧
      related state stopped

theorem MatchesStuck.refl {State Event Verdict Request : Type}
    (machine : Machine State Event Verdict Request) : MatchesStuck machine machine Eq 1 := by
  rintro state _ rfl blocked
  exact ⟨1, Nat.le_refl _, state, machine.run_succ_stuck (fuel := 0) blocked, rfl⟩

/-- Relabeling observations retains the absent-transition contract at the
same cost, even when labels are mapped noninjectively. -/
theorem MatchesStuck.relabel {Source Target Event Event' Verdict Verdict' Request Request' : Type}
    {source : Machine Source Event Verdict Request} {target : Machine Target Event Verdict Request}
    {related : Source → Target → Prop} {cost : Nat}
    (stuck : MatchesStuck source target related cost)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    MatchesStuck (source.relabel events verdicts requests) (target.relabel events verdicts requests)
      related cost := by
  intro state state' retained blocked
  have original : source.step state = none := by
    cases found : source.step state with
    | none => rfl
    | some transition => simp only [Machine.relabel, found, Option.map_some, reduceCtorEq] at blocked
  obtain ⟨count, bound, stopped, ran, retainedStopped⟩ := stuck retained original
  refine ⟨count, bound, stopped, ?_, retainedStopped⟩
  simp only [Machine.run_relabel, ran, List.map_nil, Outcome.relabel]

namespace MatchesStuck

variable {Source Target Event Verdict Request Value Failure : Type}
  {source : Machine Source Event Verdict Request}
  {target : Machine Target Event Verdict Request}
  {related : Source → Target → Prop} {cost : Nat}

/-- Closing requests cannot change an absent transition, so the original
stuck-endpoint law survives independently of the callback's response policy. -/
theorem closed (stuck : MatchesStuck source target related cost)
    (sourceCallback : Callback Source Event Request Value Failure)
    (targetCallback : Callback Target Event Request Value Failure)
    (environment : Environment Request Event Value Failure) :
    MatchesStuck (source.close sourceCallback environment)
      (target.close targetCallback environment) related cost := by
  intro state state' retained blocked
  have missing : source.step state = none := by
    cases found : source.step state with
    | none => rfl
    | some transition => simp only [Machine.close, found, Option.map_some, reduceCtorEq] at blocked
  obtain ⟨count, bound, stopped, ran, relatedStopped⟩ := stuck retained missing
  exact ⟨count, bound, stopped, target.close_run_of_no_request targetCallback environment
    count state' [] (.stuck stopped) ran, relatedStopped⟩

end MatchesStuck

namespace CostSimulation

variable {Source Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {target : Machine Target Event Verdict Request}
  {related : Source → Target → Prop} {cost : ℕ}

/-- A proved simulation survives observation relabeling at the same cost. -/
theorem relabel {Event' Verdict' Request' : Type} (simulation : CostSimulation source target related cost)
    (events : Event → Event') (verdicts : Verdict → Verdict') (requests : Request → Request') :
    CostSimulation (source.relabel events verdicts requests) (target.relabel events verdicts requests) related cost where
  silent := by
    intro state state' next relatedStates computed
    obtain ⟨original, stepped, mapped⟩ := (source.relabel_step_iff events verdicts requests state _).mp computed
    cases original with
    | silent following =>
        have same : following = next := by simpa only [Transition.relabel, Transition.silent.injEq] using mapped
        rw [← same]
        obtain ⟨count, bound, following', reached, retained⟩ := simulation.silent relatedStates stepped
        refine ⟨count, bound, following', ?_, retained⟩
        simp only [Machine.run_relabel, reached, List.map_nil, Outcome.relabel]
    | publish published following | finish verdict | fail faults | call request saved => cases mapped
  publish := by
    intro state state' published next relatedStates computed
    obtain ⟨original, stepped, mapped⟩ := (source.relabel_step_iff events verdicts requests state _).mp computed
    cases original with
    | publish originalEvents following =>
        have same : originalEvents.map events = published ∧ following = next := by
          simpa only [Transition.relabel, Transition.publish.injEq] using mapped
        rw [← same.1, ← same.2]
        obtain ⟨count, bound, following', reached, retained⟩ := simulation.publish relatedStates stepped
        refine ⟨count, bound, following', ?_, retained⟩
        simp only [Machine.run_relabel, reached, Outcome.relabel]
    | silent following | finish verdict | fail faults | call request saved => cases mapped
  finish := by
    intro state state' verdict relatedStates computed
    obtain ⟨original, stepped, mapped⟩ := (source.relabel_step_iff events verdicts requests state _).mp computed
    cases original with
    | finish originalVerdict =>
        have same : verdicts originalVerdict = verdict := by
          simpa only [Transition.relabel, Transition.finish.injEq] using mapped
        rw [← same]
        obtain ⟨count, bound, reached⟩ := simulation.finish relatedStates stepped
        refine ⟨count, bound, ?_⟩
        simp only [Machine.run_relabel, reached, List.map_nil, Outcome.relabel]
    | silent following | publish published following | fail faults | call request saved => cases mapped
  fail := by
    intro state state' faults relatedStates computed
    obtain ⟨original, stepped, mapped⟩ := (source.relabel_step_iff events verdicts requests state _).mp computed
    cases original with
    | fail originalFaults =>
        have same : originalFaults.map events = faults := by
          simpa only [Transition.relabel, Transition.fail.injEq] using mapped
        rw [← same]
        obtain ⟨count, bound, reached⟩ := simulation.fail relatedStates stepped
        refine ⟨count, bound, ?_⟩
        simp only [Machine.run_relabel, reached, Outcome.relabel]
    | silent following | publish published following | finish verdict | call request saved => cases mapped
  call := by
    intro state state' request saved relatedStates computed
    obtain ⟨original, stepped, mapped⟩ := (source.relabel_step_iff events verdicts requests state _).mp computed
    cases original with
    | call originalRequest originalSaved =>
        have same : requests originalRequest = request ∧ originalSaved = saved := by
          simpa only [Transition.relabel, Transition.call.injEq] using mapped
        rw [← same.1, ← same.2]
        obtain ⟨count, bound, saved', reached, retained⟩ := simulation.call relatedStates stepped
        refine ⟨count, bound, saved', ?_, retained⟩
        simp only [Machine.run_relabel, reached, List.map_nil, Outcome.relabel]
    | silent following | publish published following | finish verdict | fail faults => cases mapped

private theorem prefix_prepend {events : List Event} {first second : Observation Event Verdict}
    (prefixed : first.Prefix second) :
    (⟨events ++ first.events, first.status⟩ : Observation Event Verdict).Prefix
      ⟨events ++ second.events, second.status⟩ := by
  refine ⟨List.prefix_append_right_inj events |>.mpr prefixed.1, fun final => ?_⟩
  have same := prefixed.2 final
  rw [same]

/-- **Relation-level transport**: a source run's observation is a prefix of the
related target run's observation at `cost` times the fuel; when the source run
is final, the target run is the same final observation. -/
theorem observe_prefix (simulation : CostSimulation source target related cost) (fuel : ℕ)
    {state : Source} {state' : Target} (relatedStates : related state state') :
    (source.observe fuel state).Prefix (target.observe (cost * fuel) state') := by
  induction fuel generalizing state state' with
  | zero => exact ⟨List.nil_prefix, fun final => final.elim⟩
  | succ fuel ih =>
      have budget : ∀ k ≤ cost, ∃ rest, cost * (fuel + 1) = k + rest ∧ cost * fuel ≤ rest := by
        intro k bound
        exact ⟨cost * (fuel + 1) - k, by rw [Nat.mul_succ]; omega, by rw [Nat.mul_succ]; omega⟩
      cases found : source.step state with
      | none =>
          rw [source.stuck_incomplete state found]
          exact ⟨List.nil_prefix, fun final => final.elim⟩
      | some transition =>
          cases transition with
          | silent next =>
              obtain ⟨k, bound, next', ran, relatedNext⟩ := simulation.silent relatedStates found
              obtain ⟨rest, split, enough⟩ := budget k bound
              have later := (ih relatedNext).trans (target.observe_prefix_of_le enough next')
              have targetRun : target.observe (cost * (fuel + 1)) state' = target.observe rest next' := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  List.nil_append]
              rw [targetRun]
              simpa only [Machine.observe, Machine.run, found] using later
          | publish events next =>
              obtain ⟨k, bound, next', ran, relatedNext⟩ := simulation.publish relatedStates found
              obtain ⟨rest, split, enough⟩ := budget k bound
              have later := (ih relatedNext).trans (target.observe_prefix_of_le enough next')
              have targetRun : target.observe (cost * (fuel + 1)) state' =
                  ⟨events ++ (target.observe rest next').events, (target.observe rest next').status⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun]
              rw [targetRun]
              have sourceRun : source.observe (fuel + 1) state =
                  ⟨events ++ (source.observe fuel next).events, (source.observe fuel next).status⟩ := by
                simp only [Machine.observe, Machine.run, found]
              rw [sourceRun]
              exact prefix_prepend later
          | finish verdict =>
              obtain ⟨k, bound, ran⟩ := simulation.finish relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨[], .finished verdict⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _
          | fail events =>
              obtain ⟨k, bound, ran⟩ := simulation.fail relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨events, .faulted⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _
          | call request saved =>
              obtain ⟨k, bound, saved', ran, _⟩ := simulation.call relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨[], .suspended⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _

/-- **With a simulation each way, final observations coincide.** -/
theorem final_eq (forward : CostSimulation source target related cost)
    {cost' : ℕ} (backward : CostSimulation target source (fun state' state => related state state') cost')
    {state : Source} {state' : Target} (relatedStates : related state state')
    {fuel fuel' : ℕ} (final : (source.observe fuel state).status.Final)
    (final' : (target.observe fuel' state').status.Final) :
    source.observe fuel state = target.observe fuel' state' := by
  have there := forward.observe_prefix fuel relatedStates
  have back := backward.observe_prefix fuel' relatedStates
  have one := there.2 final
  have two := back.2 final'
  have sameAtTarget : target.observe (cost * fuel) state' = target.observe fuel' state' := by
    rcases le_total (cost * fuel) fuel' with le | le
    · have grown := (target.observe_prefix_of_le le state').2 (one ▸ final)
      exact grown
    · exact ((target.observe_prefix_of_le le state').2 final').symm
  exact one.trans sameAtTarget

/-- **A source state that never completes has related target states that never
complete**, given the backward simulation. -/
theorem never_completes {cost' : ℕ}
    (backward : CostSimulation target source (fun state' state => related state state') cost')
    {state : Source} {state' : Target} (relatedStates : related state state')
    (never : ∀ fuel, ¬ (source.observe fuel state).status.Final) (fuel : ℕ) :
    ¬ (target.observe fuel state').status.Final := by
  intro final
  have back := backward.observe_prefix fuel relatedStates
  have same := back.2 final
  apply never (cost' * fuel)
  rw [← same]
  exact final

/-- A callback closure preserves a simulation when the actual call/reply
events agree and the supplied reply resumes related saved continuations.
The environment returns a finite event list and a reply atomically. The cost
bounds machine transitions; it does not bound the environment's internal work. -/
theorem closed {Value Failure : Type} (simulation : CostSimulation source target related cost)
    (sourceCallback : Callback Source Event Request Value Failure)
    (targetCallback : Callback Target Event Request Value Failure)
    (environment : Environment Request Event Value Failure)
    (calls : sourceCallback.callEvent = targetCallback.callEvent)
    (replies : sourceCallback.replyEvent = targetCallback.replyEvent)
    (resumed : ∀ {saved saved'}, related saved saved' → ∀ reply,
      related (sourceCallback.resume saved reply) (targetCallback.resume saved' reply)) :
    CostSimulation (source.close sourceCallback environment)
      (target.close targetCallback environment) related cost where
  silent := by
    intro state state' next retained stepped
    cases found : source.step state with
    | none => simp only [Machine.close, found, Option.map_none, reduceCtorEq] at stepped
    | some transition =>
        cases transition <;>
          simp only [Machine.close, found, Option.map_some, Option.some.injEq,
            Transition.silent.injEq, reduceCtorEq] at stepped
        subst next
        obtain ⟨count, bound, next', ran, relatedNext⟩ := simulation.silent retained found
        exact ⟨count, bound, next', target.close_run_of_no_request targetCallback environment
          count state' [] (.exhausted next') ran, relatedNext⟩
  publish := by
    intro state state' events next retained stepped
    cases found : source.step state with
    | none => simp only [Machine.close, found, Option.map_none, reduceCtorEq] at stepped
    | some transition =>
        cases transition with
        | silent following | finish verdict | fail faults =>
            simp only [Machine.close, found, Option.map_some, Option.some.injEq, reduceCtorEq] at stepped
        | publish published following =>
            simp only [Machine.close, found, Option.map_some, Option.some.injEq,
              Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨count, bound, next', ran, relatedNext⟩ := simulation.publish retained found
            exact ⟨count, bound, next', target.close_run_of_no_request targetCallback environment
              count state' published (.exhausted next') ran, relatedNext⟩
        | call request saved =>
            simp only [Machine.close, found, Option.map_some, Option.some.injEq,
              Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨count, bound, saved', ran, relatedSaved⟩ := simulation.call retained found
            obtain ⟨closedCount, closedBound, closedRun⟩ :=
              target.close_run_of_suspended targetCallback environment count state' [] request saved' ran
            refine ⟨closedCount, closedBound.trans bound,
              targetCallback.resume saved' (environment request).2, ?_, resumed relatedSaved _⟩
            simpa only [List.nil_append, Machine.callEvents, calls, replies] using closedRun
  finish := by
    intro state state' verdict retained stepped
    cases found : source.step state with
    | none => simp only [Machine.close, found, Option.map_none, reduceCtorEq] at stepped
    | some transition =>
        cases transition <;>
          simp only [Machine.close, found, Option.map_some, Option.some.injEq,
            Transition.finish.injEq, reduceCtorEq] at stepped
        subst verdict
        obtain ⟨count, bound, ran⟩ := simulation.finish retained found
        exact ⟨count, bound, target.close_run_of_no_request targetCallback environment
          count state' [] (.finished _) ran⟩
  fail := by
    intro state state' events retained stepped
    cases found : source.step state with
    | none => simp only [Machine.close, found, Option.map_none, reduceCtorEq] at stepped
    | some transition =>
        cases transition <;>
          simp only [Machine.close, found, Option.map_some, Option.some.injEq,
            Transition.fail.injEq, reduceCtorEq] at stepped
        subst events
        obtain ⟨count, bound, ran⟩ := simulation.fail retained found
        exact ⟨count, bound, target.close_run_of_no_request targetCallback environment
          count state' _ .faulted ran⟩
  call := by
    intro _ _ request
    exact request.elim


end CostSimulation

/-! ## Resumable callback execution -/

/-- A caller runs, or waits while a service retains its own execution state.
The saved caller and request remain available across every service step. -/
inductive HandledState (State Service Request : Type) where
  | running (state : State)
  | handling (request : Request) (saved : State) (service : Service)
  deriving DecidableEq, Repr

/-- Lift a service's external-response protocol through its retained caller.
This is a state adapter, not a permission to supply unsolicited replies.
External calls of `Machine.handle` always save a `handling` state. -/
def Callback.throughHandler {State Service Event Request External Value Failure : Type}
    (callback : Callback Service Event External Value Failure) :
    Callback (HandledState State Service Request) Event External Value Failure where
  callEvent := callback.callEvent
  replyEvent := callback.replyEvent
  resume
    | .running state, _ => .running state
    | .handling request saved state, reply => .handling request saved (callback.resume state reply)

namespace Machine

variable {State Service Event Verdict Request External Value Failure : Type}
variable (machine : Machine State Event Verdict Request)
variable (callback : Callback State Event Request Value Failure)
variable (service : Machine Service Event (Reply Value Failure) External)
variable (load : Request → Service)

/-- Execute each callback as a machine. Call and reply boundaries are visible;
the service may suspend, diverge, fault or become stuck before replying. -/
def handle : Machine (HandledState State Service Request) Event Verdict External where
  step
    | .running state => (machine.step state).map fun
        | .silent next => .silent (.running next)
        | .publish events next => .publish events (.running next)
        | .finish verdict => .finish verdict
        | .fail events => .fail events
        | .call request saved =>
            .publish [callback.callEvent request] (.handling request saved (load request))
    | .handling request saved state => (service.step state).map fun
        | .silent next => .silent (.handling request saved next)
        | .publish events next => .publish events (.handling request saved next)
        | .finish reply =>
            .publish [callback.replyEvent reply] (.running (callback.resume saved reply))
        | .fail events => .fail events
        | .call external retained => .call external (.handling request saved retained)

/-- All external calls originate inside the service and save both levels of
continuation. The running-caller branch of `throughHandler` is unreachable
at an external call boundary. -/
theorem handle_call_iff (state saved : HandledState State Service Request) (external : External) :
    (machine.handle callback service load).step state = some (.call external saved) ↔
      ∃ request caller active retained,
        state = .handling request caller active ∧
        service.step active = some (.call external retained) ∧
        saved = .handling request caller retained := by
  cases state with
  | running state =>
      cases found : machine.step state with
      | none => simp [handle, found]
      | some transition => cases transition <;> simp [handle, found]
  | handling request caller active =>
      cases found : service.step active with
      | none => simp [handle, found]
      | some transition =>
          cases transition <;> simp [handle, found, eq_comm]

/-- Handling a service's further requests before composition or afterwards
gives the same machine, including every saved endpoint and boundary event. -/
theorem handle_close {ExternalValue ExternalFailure : Type}
    (externalCallback : Callback Service Event External ExternalValue ExternalFailure)
    (environment : Environment External Event ExternalValue ExternalFailure) :
    (machine.handle callback service load).close externalCallback.throughHandler environment =
      machine.handle callback (service.close externalCallback environment) load := by
  apply congrArg (fun step => (⟨step⟩ : Machine (HandledState State Service Request) Event Verdict Empty))
  funext state
  cases state with
  | running state =>
      cases found : machine.step state with
      | none => simp [handle, found]
      | some transition => cases transition <;> simp [handle, found]
  | handling request saved state =>
      cases found : service.step state with
      | none => simp [handle, close, found]
      | some transition =>
          cases transition <;> simp [handle, close, found, Callback.throughHandler, callEvents]

/-- Read a service outcome inside its retained caller. Finishing the service
resumes the caller; it does not finish the caller's computation. -/
def handlerOutcome (request : Request) (saved : State) :
    Outcome Service (Reply Value Failure) External →
      Outcome (HandledState State Service Request) Verdict External
  | .finished reply => .exhausted (.running (callback.resume saved reply))
  | .faulted => .faulted
  | .suspended external retained => .suspended external (.handling request saved retained)
  | .stuck state => .stuck (.handling request saved state)
  | .exhausted state => .exhausted (.handling request saved state)

/-- Before a reply, the embedded service has exactly its original events,
budget and outcome, with the caller attached to its complete residual. -/
theorem handle_run_of_no_reply (fuel : Nat) (request : Request) (saved : State)
    (state : Service) (events : List Event) (outcome : Outcome Service (Reply Value Failure) External)
    (ran : service.run fuel state = (events, outcome))
    (noReply : ∀ reply, outcome ≠ .finished reply) :
    (machine.handle callback service load).run fuel (.handling request saved state) =
      (events, handlerOutcome callback request saved outcome) := by
  induction fuel generalizing state events outcome with
  | zero =>
      simp only [run, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      rfl
  | succ fuel ih =>
      cases found : service.step state with
      | none =>
          simp only [run, found, Prod.mk.injEq] at ran
          obtain ⟨rfl, rfl⟩ := ran
          simp only [run, handle, found, Option.map_none, handlerOutcome]
      | some transition =>
          cases transition with
          | silent next =>
              rw [service.run_succ_silent found] at ran
              simpa only [run, handle, found, Option.map_some] using ih next events outcome ran noReply
          | publish published next =>
              rw [service.run_succ_publish found] at ran
              have same := Prod.mk.inj ran
              have child : service.run fuel next = ((service.run fuel next).1, outcome) :=
                Prod.ext rfl same.2
              have resumed := ih next (service.run fuel next).1 outcome child noReply
              have stepped : (machine.handle callback service load).step (.handling request saved state) =
                  some (.publish published (.handling request saved next)) := by simp [handle, found]
              rw [(machine.handle callback service load).run_succ_publish stepped, resumed]
              exact Prod.ext same.1 rfl
          | finish reply =>
              rw [service.run_succ_finish found] at ran
              exact False.elim (noReply reply (Prod.mk.inj ran).2.symm)
          | fail faults =>
              simp only [run, found, Prod.mk.injEq] at ran
              obtain ⟨rfl, rfl⟩ := ran
              simp only [run, handle, found, Option.map_some, handlerOutcome]
          | call external retained =>
              simp only [run, found, Prod.mk.injEq] at ran
              obtain ⟨rfl, rfl⟩ := ran
              simp only [run, handle, found, Option.map_some, handlerOutcome]

/-- A completed service run emits one reply boundary and returns the exact
resumed caller. Unused service fuel is not silently spent in the caller. -/
theorem handle_run_of_reply (fuel : Nat) (request : Request) (saved : State)
    (state : Service) (events : List Event) (reply : Reply Value Failure)
    (ran : service.run fuel state = (events, .finished reply)) :
    ∃ used ≤ fuel,
      (machine.handle callback service load).run used (.handling request saved state) =
        (events ++ [callback.replyEvent reply], .exhausted (.running (callback.resume saved reply))) := by
  induction fuel generalizing state events with
  | zero => simp [run] at ran
  | succ fuel ih =>
      cases found : service.step state with
      | none => simp [run, found] at ran
      | some transition =>
          cases transition with
          | silent next =>
              rw [service.run_succ_silent found] at ran
              obtain ⟨used, bound, executed⟩ := ih next events ran
              exact ⟨used + 1, by omega, by simpa only [run, handle, found, Option.map_some] using executed⟩
          | publish published next =>
              rw [service.run_succ_publish found] at ran
              have same := Prod.mk.inj ran
              obtain ⟨used, bound, executed⟩ := ih next (service.run fuel next).1 (Prod.ext rfl same.2)
              refine ⟨used + 1, by omega, ?_⟩
              have stepped : (machine.handle callback service load).step (.handling request saved state) =
                  some (.publish published (.handling request saved next)) := by simp [handle, found]
              rw [(machine.handle callback service load).run_succ_publish stepped, executed]
              simp only [← same.1, List.append_assoc]
          | finish result =>
              simp only [run, found, Prod.mk.injEq, Outcome.finished.injEq] at ran
              obtain ⟨rfl, rfl⟩ := ran
              exact ⟨1, by omega, by simp [run, handle, found]⟩
          | fail faults => simp [run, found] at ran
          | call external retained => simp [run, found] at ran

/-- Service divergence is retained, rather than converted to a fictitious
atomic reply. This does not assert termination of either machine. -/
theorem handle_divergesWithin (request : Request) (saved : State) (state : Service)
    (diverges : service.DivergesWithin state) :
    (machine.handle callback service load).DivergesWithin (.handling request saved state) := by
  intro fuel
  obtain ⟨residual, ran⟩ := diverges fuel
  refine ⟨.handling request saved residual, ?_⟩
  have executed := machine.handle_run_of_no_reply callback service load fuel request saved state
    (service.run fuel state).1 (.exhausted residual) (Prod.ext rfl ran) (by intro reply impossible; cases impossible)
  exact congrArg Prod.snd executed

/-- A call and a terminating service execution realize the complete callback
trace. Its transition bound includes entry into the service. -/
theorem handle_call_run (state saved : State) (request : Request)
    (called : machine.step state = some (.call request saved))
    (fuel : Nat) (events : List Event) (reply : Reply Value Failure)
    (answered : service.run fuel (load request) = (events, .finished reply)) :
    ∃ used ≤ fuel + 1,
      (machine.handle callback service load).run used (.running state) =
        (callback.callEvent request :: events ++ [callback.replyEvent reply],
          .exhausted (.running (callback.resume saved reply))) := by
  obtain ⟨used, bound, ran⟩ :=
    machine.handle_run_of_reply callback service load fuel request saved (load request) events reply answered
  refine ⟨used + 1, by omega, ?_⟩
  have stepped : (machine.handle callback service load).step (.running state) =
      some (.publish [callback.callEvent request] (.handling request saved (load request))) := by
    simp [handle, called]
  rw [(machine.handle callback service load).run_succ_publish stepped, ran]
  rfl

/-- Calls and replies are visible, so silent work stays inside one component.
The existing ranks therefore bound administration in the composite. -/
def Productive.handled (callerProgress : machine.Productive) (serviceProgress : service.Productive) :
    (machine.handle callback service load).Productive where
  rank
    | .running state => callerProgress.rank state
    | .handling _ _ state => serviceProgress.rank state
  silent_decreases := by
    intro state next stepped
    cases state with
    | running state =>
        cases found : machine.step state with
        | none => simp [handle, found] at stepped
        | some transition =>
            cases transition <;> simp [handle, found] at stepped
            subst next
            exact callerProgress.silent_decreases found
    | handling request saved state =>
        cases found : service.step state with
        | none => simp [handle, found] at stepped
        | some transition =>
            cases transition <;> simp [handle, found] at stepped
            subst next
            exact serviceProgress.silent_decreases found
  moves := by
    intro state
    cases state with
    | running state => simpa [handle] using callerProgress.moves state
    | handling request saved state => simpa [handle] using serviceProgress.moves state

/-- Atomic callbacks refine to resumable service execution when the service
actually computes the declared environment response within a uniform bound.
The representation retains the caller state; no service termination premise
is required by `handle` itself. -/
theorem close_handle_costSimulation
    (service : Machine Service Event (Reply Value Failure) Empty)
    (environment : Environment Request Event Value Failure) (bound : Nat)
    (answers : ∀ request, service.run bound (load request) =
      ((environment request).1, .finished (environment request).2)) :
    CostSimulation (machine.close callback environment) (machine.handle callback service load)
      (fun state retained => retained = .running state) (bound + 1) where
  silent := by
    rintro state _ next rfl stepped
    cases found : machine.step state with
    | none => simp [close, found] at stepped
    | some transition =>
        cases transition <;> simp [close, found] at stepped
        subst next
        refine ⟨1, by omega, .running _, ?_, rfl⟩
        simp [run, handle, found]
  publish := by
    rintro state _ events next rfl stepped
    cases found : machine.step state with
    | none => simp [close, found] at stepped
    | some transition =>
        cases transition with
        | silent next => simp [close, found] at stepped
        | publish published retained =>
            simp only [close, found, Option.map_some, Option.some.injEq, Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            refine ⟨1, by omega, .running retained, ?_, rfl⟩
            simp [run, handle, found]
        | finish verdict => simp [close, found] at stepped
        | fail faults => simp [close, found] at stepped
        | call request saved =>
            simp only [close, found, Option.map_some, Option.some.injEq, Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨used, within, ran⟩ := machine.handle_call_run callback service load state saved request found
              bound (environment request).1 (environment request).2 (answers request)
            exact ⟨used, within, .running _, ran, rfl⟩
  finish := by
    rintro state _ verdict rfl stepped
    cases found : machine.step state with
    | none => simp [close, found] at stepped
    | some transition =>
        cases transition <;> simp [close, found] at stepped
        subst verdict
        exact ⟨1, by omega, by simp [run, handle, found]⟩
  fail := by
    rintro state _ events rfl stepped
    cases found : machine.step state with
    | none => simp [close, found] at stepped
    | some transition =>
        cases transition <;> simp [close, found] at stepped
        subst events
        exact ⟨1, by omega, by simp [run, handle, found]⟩
  call := by
    intro state retained request
    exact request.elim

/-- The constructed atomic/resumable representation also preserves stuck
endpoints, which transition simulation alone does not assert. -/
theorem close_handle_matchesStuck
    (service : Machine Service Event (Reply Value Failure) Empty)
    (environment : Environment Request Event Value Failure) (bound : Nat) :
    MatchesStuck (machine.close callback environment) (machine.handle callback service load)
      (fun state retained => retained = .running state) (bound + 1) := by
  rintro state _ rfl blocked
  have absent : machine.step state = none := by simpa [close] using blocked
  refine ⟨1, by omega, .running state, ?_, rfl⟩
  simp [run, handle, absent]

end Machine

end Mettapedia.GSLT.Distinction.ProductiveBlocks
