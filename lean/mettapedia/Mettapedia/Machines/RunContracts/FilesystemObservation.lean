import Mettapedia.Machines.RunContracts.TypedFailure

/-!
# Finite filesystem observation and resumable collection

An input is a finite sequence of observations supplied by a provider, not an
immutable filesystem snapshot. End is an explicit observation; running out of
available observations or budget establishes no end. Data payloads may be empty.
The collector is checked against an independent transition judgment. Resuming
uses the unconsumed suffix and preserves ordered, possibly equal occurrences.

These are protocol results. They do not prove native syscall correspondence,
liveness, concurrent cursor safety or facts about future filesystem changes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.FilesystemObservation

universe u v w
variable {α : Type u} {ε : Type v} {Reason : Type w}

inductive Event (α : Type u) (ε : Type v) (Reason : Type w) where
  | data (value : α)
  | ended
  | fault (value : ε)
  | interrupted (reason : Reason)
  deriving DecidableEq, Repr

inductive Stop (ε : Type v) (Reason : Type w) where
  | ended
  | fault (value : ε)
  | interrupted (reason : Reason)
  | paused
  deriving DecidableEq, Repr

structure Report (α : Type u) (ε : Type v) (Reason : Type w) where
  values : List α
  stop : Stop ε Reason
  remaining : List (Event α ε Reason)
  deriving DecidableEq, Repr

def prepend (value : α) (report : Report α ε Reason) : Report α ε Reason :=
  {report with values := value :: report.values}

/-- Consume up to a budget of observations, stopping at the first terminal.
An exhausted input buffer is paused, not a manufactured end event. -/
def collect : Nat → List (Event α ε Reason) → Report α ε Reason
  | 0, input => ⟨[], .paused, input⟩
  | _ + 1, [] => ⟨[], .paused, []⟩
  | fuel + 1, .data value :: input => prepend value (collect fuel input)
  | _ + 1, .ended :: input => ⟨[], .ended, input⟩
  | _ + 1, .fault value :: input => ⟨[], .fault value, input⟩
  | _ + 1, .interrupted reason :: input => ⟨[], .interrupted reason, input⟩

/-- Independent ordered transition judgment. Equal payloads remain two steps. -/
inductive Observes : Nat → List (Event α ε Reason) →
    List α → Stop ε Reason → List (Event α ε Reason) → Prop where
  | budget (input) : Observes 0 input [] .paused input
  | unavailable (fuel) : Observes (fuel + 1) [] [] .paused []
  | data {fuel input values stop remaining} (value : α)
      (next : Observes fuel input values stop remaining) :
      Observes (fuel + 1) (.data value :: input) (value :: values) stop remaining
  | ended (fuel input) : Observes (fuel + 1) (.ended :: input) [] .ended input
  | fault (fuel input) (value : ε) :
      Observes (fuel + 1) (.fault value :: input) [] (.fault value) input
  | interrupted (fuel input) (reason : Reason) :
      Observes (fuel + 1) (.interrupted reason :: input) [] (.interrupted reason) input

theorem Observes.sound {fuel input values stop remaining}
    (observed : Observes (α := α) (ε := ε) (Reason := Reason)
      fuel input values stop remaining) :
    collect fuel input = ⟨values, stop, remaining⟩ := by
  induction observed with
  | budget => rfl
  | unavailable => rfl
  | data value next ih => simp [collect, prepend, ih]
  | ended => rfl
  | fault => rfl
  | interrupted => rfl

theorem Observes.complete (fuel : Nat) (input : List (Event α ε Reason)) :
    Observes fuel input (collect fuel input).values (collect fuel input).stop
      (collect fuel input).remaining := by
  induction fuel generalizing input with
  | zero => exact .budget input
  | succ fuel ih =>
      cases input with
      | nil => exact .unavailable fuel
      | cons event input =>
          cases event with
          | data value => exact .data value (ih input)
          | ended => exact .ended fuel input
          | fault value => exact .fault fuel input value
          | interrupted reason => exact .interrupted fuel input reason

theorem collect_iff (fuel : Nat) (input : List (Event α ε Reason))
    (report : Report α ε Reason) :
    collect fuel input = report ↔
      Observes fuel input report.values report.stop report.remaining := by
  constructor
  · intro same
    exact same ▸ Observes.complete fuel input
  · intro observed
    exact observed.sound

/-- Only a paused residual can be resumed. A terminal report is not a licence
to execute later observations, reinterpret a fault or retry an unknown effect. -/
def resume (fuel : Nat) (earlier : Report α ε Reason) : Report α ε Reason :=
  match earlier.stop with
  | .paused =>
      let suffix := collect fuel earlier.remaining
      {suffix with values := earlier.values ++ suffix.values}
  | _ => earlier

@[simp] theorem collect_nil (fuel : Nat) :
    collect (α := α) (ε := ε) (Reason := Reason) fuel [] = ⟨[], .paused, []⟩ := by
  cases fuel <;> rfl

theorem resume_prepend (fuel : Nat) (value : α) (report : Report α ε Reason) :
    resume fuel (prepend value report) = prepend value (resume fuel report) := by
  cases report with
  | mk values stop remaining =>
      cases stop <;> simp [resume, prepend]

/-- Partitioning a budget consumes the same observations exactly once,
retaining order, multiplicity and the precise terminal reason. -/
theorem collect_add (first second : Nat) (input : List (Event α ε Reason)) :
    collect (first + second) input = resume second (collect first input) := by
  induction first generalizing input with
  | zero => simp [collect, resume]
  | succ first ih =>
      cases input with
      | nil => simp [resume]
      | cons event input =>
          cases event with
          | data value => simp [Nat.succ_add, collect, ih, resume_prepend]
          | ended => simp [Nat.succ_add, collect, resume]
          | fault value => simp [Nat.succ_add, collect, resume]
          | interrupted reason => simp [Nat.succ_add, collect, resume]

/-- A paused report's consumed prefix consists precisely of its delivered
data occurrences. Resumption starts at the untouched suffix, not the source. -/
theorem paused_decomposition (fuel : Nat) (input : List (Event α ε Reason))
    (paused : (collect fuel input).stop = .paused) :
    input = (collect fuel input).values.map Event.data ++ (collect fuel input).remaining := by
  induction fuel generalizing input with
  | zero => rfl
  | succ fuel ih =>
      cases input with
      | nil => rfl
      | cons event input =>
          cases event with
          | data value =>
              have rest := ih input paused
              simpa [collect, prepend] using congrArg (List.cons (.data value)) rest
          | ended => simp [collect] at paused
          | fault value => simp [collect] at paused
          | interrupted reason => simp [collect] at paused

def ClosedZero (report : Report α ε Reason) : Prop :=
  report.values = [] ∧ report.stop = .ended

theorem paused_not_closed_zero (values : List α) (remaining : List (Event α ε Reason)) :
    ¬ ClosedZero (Report.mk values .paused remaining) := by simp [ClosedZero]

theorem fault_not_closed_zero (values : List α) (fault : ε)
    (remaining : List (Event α ε Reason)) :
    ¬ ClosedZero (Report.mk values (.fault fault) remaining) := by simp [ClosedZero]

theorem interrupted_not_closed_zero (values : List α) (reason : Reason)
    (remaining : List (Event α ε Reason)) :
    ¬ ClosedZero (Report.mk values (.interrupted reason) remaining) := by simp [ClosedZero]

theorem empty_data_not_closed_zero (remaining : List (Event (List α) ε Reason)) :
    ¬ ClosedZero (collect 1 (.data [] :: remaining)) := by simp [ClosedZero, collect, prepend]

/-- Observing end does not consume or certify anything about a later event. -/
theorem end_keeps_future (fuel : Nat) (future : List (Event α ε Reason)) :
    collect (fuel + 1) (.ended :: future) = ⟨[], .ended, future⟩ := rfl

theorem terminal_not_retried (fuel : Nat) (report : Report α ε Reason)
    (terminal : report.stop ≠ .paused) : resume fuel report = report := by
  cases report with
  | mk values stop remaining => cases stop <;> simp_all [resume]

theorem completed_empty_has_end_witness (fuel : Nat) (input : List (Event α ε Reason))
    (completed : ClosedZero (collect fuel input)) : Event.ended ∈ input := by
  cases fuel with
  | zero => simp [ClosedZero, collect] at completed
  | succ fuel =>
      cases input with
      | nil => simp [ClosedZero] at completed
      | cons event input =>
          cases event with
          | data value => simp [ClosedZero, collect, prepend] at completed
          | ended => simp
          | fault value => simp [ClosedZero, collect] at completed
          | interrupted reason => simp [ClosedZero, collect] at completed

example : (collect (ε := String) (Reason := String) 3
    [.data "same", .data "same", .ended]).values = ["same", "same"] := rfl

example : ¬ ClosedZero (collect (α := String) (ε := String) (Reason := String) 0 [.ended]) := by
  simp [ClosedZero, collect]

example : (collect (ε := String) (Reason := String) 2 [.data "first", .fault "read-failed"]).stop =
    .fault "read-failed" := rfl

end Mettapedia.Machines.RunContracts.FilesystemObservation
