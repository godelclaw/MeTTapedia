import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention.PollLoop
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns
import Mettapedia.Machines.RefusalObservation

/-!
# The retained refusal is a fair run; the counted refusal is the existing refusal semantics

Two connections for the native rule of `PollLoop`.

## Fairness does not help (`OccurrenceCommits.Liveness.FairRuns`)

The reader's world is a labelled transition system (`nativeSystem`): the reader waits (a refused
poll, which is also the idle step of a finished reader), completes (a permitted poll), or an
environment event changes its context. The `wait` and `complete` steps are exactly the native
`poll` (`next_wait`, `next_complete`).

* From a pending reader whose call is unjustified, **every run** keeps the reader pending and
  never completes (`run_never_completes`), and every such run is strongly fair for completion,
  because completion is never enabled (`run_stronglyFair_completion`).
* **A run strongly fair for every step kind still never completes** (`fair_livelock`): with
  finitely many events, the aging scheduler of `FairRuns` gives a run from that reader that is
  strongly fair for completion, for waiting and for every environment event, and in it the reader
  is never observed. The failure is not a scheduling failure, so no fairness assumption repairs
  it: the rule itself must change (`PollLoop.pollObliged`).
* The attempt model of `Liveness.OptimisticRetries` refuses differently: a refused commit is not an
  allowed step, so its bounded lock-freedom (`OptimisticRetries.Run.commit_within`) holds for every
  refusal policy. The native wait is an allowed step that changes nothing but the poll count, which
  is why that bound does not reach it.

## The counted refusal is `RefusalObservation`'s semantics (`Machines.RefusalObservation`)

* `RefusalObservation` models a refused acquisition as a failed attempt: its machine continues
  with the refusal branch, a strictly smaller search, so every run ends. **The native retry of the
  same acquisition is not one of its searches** (`retry_is_not_a_search`): no search is its own
  refusal branch. Its theorem `refusal_is_incomplete` therefore says nothing about the native
  retained-refusal path.
* **The counted rule realizes it on a single call** (`pollCounted_realizes_refusalObservation`):
  the observation of the counted rule, read as an exact answer bag or an incomplete run, is the
  observation of the one-acquisition search under the same refusal. The native rule departs from
  it on every refused call (`poll_departs_from_refusalObservation`): the search is observed
  incomplete; the native reader is never observed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

universe u v w x

variable {Ctx : Type u} {Task : Type v} {Value : Type w} {E : Type x}

/-! ## The reader's world as a labelled transition system -/

/-- A step of the reader's world. -/
inductive Label (E : Type x)
  | wait : Label E
  | complete : Label E
  | event : E → Label E

/-- **The native rule as a labelled transition system.** Waiting is allowed to a pending reader
whose call is refused, and to a finished reader as its idle step; completion to a pending reader
whose call is permitted; an environment event at any time. -/
def nativeSystem (apply : E → Ctx → Ctx) (permit : Ctx → Task → Bool) (run : Task → Value) :
    LTS (Reader Ctx Task Value) (Label E) where
  Allowed r
    | .wait => r.observed = none → permit r.ctx r.task = false
    | .complete => r.observed = none ∧ permit r.ctx r.task = true
    | .event _ => True
  next r
    | .wait => { r with polls := r.polls + 1 }
    | .complete => { r with observed := some (.value (run r.task)), polls := r.polls + 1 }
    | .event e => { r with ctx := apply e r.ctx }

section System

variable (apply : E → Ctx → Ctx) (permit : Ctx → Task → Bool) (run : Task → Value)

/-- A wait of a pending reader is the native poll of a refused call. -/
theorem next_wait {r : Reader Ctx Task Value} (pending : r.observed = none)
    (allowed : (nativeSystem apply permit run).Allowed r .wait) :
    (nativeSystem apply permit run).next r .wait = poll permit run r :=
  (poll_refused_retains permit run pending (allowed pending)).symm

/-- A completion is the native poll of a permitted call. -/
theorem next_complete {r : Reader Ctx Task Value}
    (allowed : (nativeSystem apply permit run).Allowed r .complete) :
    (nativeSystem apply permit run).next r .complete = poll permit run r := by
  obtain ⟨pending, permitted⟩ := allowed
  simp [nativeSystem, poll, pending, produce, permitted]

/-- The native system never blocks: a reader can always wait or complete. -/
theorem nativeSystem_nonBlocking : (nativeSystem apply permit run).NonBlocking := by
  intro r
  cases permitted : permit r.ctx r.task with
  | false => exact ⟨.wait, fun _ => permitted⟩
  | true =>
    cases seen : r.observed with
    | none => exact ⟨.complete, seen, permitted⟩
    | some _ => exact ⟨.wait, fun pending => by simp [seen] at pending⟩

/-- The completion task. -/
def completes : Label E → Prop := fun a => a = .complete

/-- Completion is enabled exactly at a pending reader whose call is permitted. -/
theorem completes_enabled_iff (r : Reader Ctx Task Value) :
    (nativeSystem apply permit run).TaskEnabled completes r ↔
      r.observed = none ∧ permit r.ctx r.task = true := by
  constructor
  · rintro ⟨a, isComplete, allowed⟩
    subst isComplete
    exact allowed
  · intro allowed
    exact ⟨.complete, rfl, allowed⟩

/-- Along any run from a pending reader with an unjustified call, the reader stays pending and
its call stays unjustified. -/
theorem run_unjustified (ρ : Run (nativeSystem apply permit run))
    (pending : (ρ.state 0).observed = none)
    (unjustified : ¬ Justified apply permit (ρ.state 0).ctx (ρ.state 0).task) (n : ℕ) :
    (ρ.state n).observed = none ∧ ¬ Justified apply permit (ρ.state n).ctx (ρ.state n).task := by
  induction n with
  | zero => exact ⟨pending, unjustified⟩
  | succ n ih =>
    obtain ⟨stillPending, stillUnjustified⟩ := ih
    have allowed := ρ.allowed n
    rw [ρ.step n]
    cases label : ρ.label n with
    | wait => exact ⟨stillPending, stillUnjustified⟩
    | complete =>
      rw [label] at allowed
      exact absurd allowed.2 (by simp [refused_of_not_justified stillUnjustified])
    | event e => exact ⟨stillPending, not_justified_apply stillUnjustified e⟩

/-- **Every run leaves an unjustified call pending forever.** -/
theorem run_never_completes (ρ : Run (nativeSystem apply permit run))
    (pending : (ρ.state 0).observed = none)
    (unjustified : ¬ Justified apply permit (ρ.state 0).ctx (ρ.state 0).task) (n : ℕ) :
    (ρ.state n).observed = none ∧ ρ.label n ≠ .complete := by
  obtain ⟨stillPending, stillUnjustified⟩ := run_unjustified apply permit run ρ pending unjustified n
  refine ⟨stillPending, fun isComplete => ?_⟩
  have allowed := ρ.allowed n
  rw [isComplete] at allowed
  exact absurd allowed.2 (by simp [refused_of_not_justified stillUnjustified])

/-- **Every such run is strongly fair for completion**, because completion is never enabled. -/
theorem run_stronglyFair_completion (ρ : Run (nativeSystem apply permit run))
    (pending : (ρ.state 0).observed = none)
    (unjustified : ¬ Justified apply permit (ρ.state 0).ctx (ρ.state 0).task) :
    ρ.StronglyFair completes := by
  intro often
  exfalso
  obtain ⟨n, _, enabled⟩ := often 0
  rw [completes_enabled_iff] at enabled
  obtain ⟨_, stillUnjustified⟩ := run_unjustified apply permit run ρ pending unjustified n
  exact absurd enabled.2 (by simp [refused_of_not_justified stillUnjustified])

/-- The step kinds of the reader's world as a finite family of tasks: completion, waiting, and
each environment event. -/
def stepTask : Option (Option E) → Label E → Prop
  | none => fun a => a = .complete
  | some none => fun a => a = .wait
  | some (some e) => fun a => a = .event e

/-- **A run strongly fair for every step kind still never completes.** With finitely many events,
some run from a pending reader whose call is unjustified is strongly fair for completion, for
waiting and for every event, and in it the reader is never observed. -/
theorem fair_livelock [Fintype E] [DecidableEq E] {r₀ : Reader Ctx Task Value}
    (pending : r₀.observed = none) (unjustified : ¬ Justified apply permit r₀.ctx r₀.task) :
    ∃ ρ : Run (nativeSystem apply permit run), ρ.state 0 = r₀ ∧
      (∀ i, ρ.StronglyFair (stepTask i)) ∧ ∀ n, (ρ.state n).observed = none := by
  obtain ⟨ρ, start, fair⟩ :=
    exists_stronglyFair_run stepTask (nativeSystem_nonBlocking apply permit run) r₀
  refine ⟨ρ, start, fair, fun n => ?_⟩
  exact (run_never_completes apply permit run ρ (by rw [start]; exact pending)
    (by rw [start]; exact unjustified) n).1

end System

/-! ## The counted refusal is `RefusalObservation`'s semantics -/

open Mettapedia.Machines.RefusalObservation in
/-- **The native retry is not a search of `RefusalObservation`**: no search is its own refusal
branch, so the machine's refusal continuation is always a smaller search. -/
theorem retry_is_not_a_search {Answer : Type w} (counted : Bool) (next s : Search Answer) :
    s ≠ Search.acquire counted next s := by
  intro same
  have sizes := congrArg Search.size same
  simp only [Search.size] at sizes
  omega

open Mettapedia.Machines.RefusalObservation in
/-- The search of a single counted call: its answer when the identity is minted, failure when it
is refused. -/
def callSearch (val : Value) : Search Value := .acquire true (.answer val) .fail

open Mettapedia.Machines.RefusalObservation in
/-- `RefusalObservation`'s observation of a single counted call, refused exactly when the permit
fails: exact when permitted, incomplete when refused. -/
theorem observe_callSearch (permitted : Bool) (val : Value) :
    observe (fun _ => !permitted) true 0 (callSearch val) =
      if permitted then .exact [val] else .incomplete := by
  cases permitted <;> simp [observe, callSearch, run_acquire, run_answer, run_fail]

open Mettapedia.Machines.RefusalObservation in
/-- A reader's observation read in `RefusalObservation`'s vocabulary: a value is an exact
one-answer bag, an explicit refusal is an incomplete run, and a pending reader has none yet. -/
def asSearchObservation : Option (Observation Value) →
    Option (Mettapedia.Machines.RefusalObservation.Observation Value)
  | none => none
  | some (.value val) => some (.exact [val])
  | some .refused => some .incomplete

open Mettapedia.Machines.RefusalObservation in
/-- **The counted rule realizes `RefusalObservation` on a single call.** -/
theorem pollCounted_realizes_refusalObservation (permit : Ctx → Task → Bool) (run : Task → Value)
    {r : Reader Ctx Task Value} (pending : r.observed = none) :
    asSearchObservation (pollCounted permit run r).observed =
      some (observe (fun _ => !(permit r.ctx r.task)) true 0 (callSearch (run r.task))) := by
  rw [observe_callSearch]
  cases permitted : permit r.ctx r.task <;>
    simp [pollCounted, pending, produce, permitted, asSearchObservation]

open Mettapedia.Machines.RefusalObservation in
/-- **The native rule departs from it on every refused call**: the search is observed incomplete,
the native reader is never observed. -/
theorem poll_departs_from_refusalObservation (permit : Ctx → Task → Bool) (run : Task → Value)
    {r : Reader Ctx Task Value} (pending : r.observed = none)
    (refused : permit r.ctx r.task = false) (n : ℕ) :
    asSearchObservation ((poll permit run)^[n] r).observed = none ∧
      observe (fun _ => !(permit r.ctx r.task)) true 0 (callSearch (run r.task)) = .incomplete := by
  refine ⟨?_, ?_⟩
  · rw [refused_never_observes permit run pending refused n]
    rfl
  · rw [observe_callSearch, refused]
    rfl

/-! ## Controls -/

namespace Controls

/-- The livelock of `PollLoop.Controls`, in a world whose only event changes nothing: a run
strongly fair for every step kind, in which the reader is never observed. -/
theorem inert_fair_livelock :
    ∃ ρ : Run (nativeSystem inert needsGrant
        answer),
      ρ.state 0 = waiting ∧ (∀ i, ρ.StronglyFair (stepTask i)) ∧
        ∀ n, (ρ.state n).observed = none :=
  fair_livelock _ _ _ rfl inert_never_completes.1

/-- In the world whose event grants, the call is justified: the completion step is reachable by
one event, so this world has no such livelock from the waiting reader. -/
theorem grants_completion_reachable :
    (nativeSystem grants needsGrant
        answer).TaskEnabled completes
      ((nativeSystem grants needsGrant
        answer).next waiting (.event ())) := by
  rw [completes_enabled_iff]
  exact ⟨rfl, rfl⟩

/-- The single-call search, refused: incomplete; permitted: the exact answer. -/
theorem callSearch_controls :
    Mettapedia.Machines.RefusalObservation.observe (fun _ => true) true 0 (callSearch 42) =
        .incomplete ∧
      Mettapedia.Machines.RefusalObservation.observe (fun _ => false) true 0 (callSearch 42) =
        .exact [42] :=
  ⟨observe_callSearch false 42, observe_callSearch true 42⟩

/-- **Completes, positive and negative**: the completion label is the completion task; waiting is
not. -/
theorem completes_controls : completes (.complete : Label Unit) ∧ ¬ completes (.wait : Label Unit) :=
  ⟨rfl, fun h => by cases h⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RefusalRetention
