import Mettapedia.Machines.RunContracts.ScopedOutcome
import Mettapedia.Machines.RunContracts.Completion

/-!
# Kind-indexed failures and honest empty-frontier observation

An operation's failure payload is indexed by its kind. Handler classes select
kinds but do not erase them. Returned data (including error-shaped data),
exhausted zero-answer search, and unfinished search are not exception kinds.
The hierarchy below is an operation-policy vocabulary, not a replacement for
language-specific no-value taxonomies. Extending it needs explicit membership
rules; an arbitrary operation result is not automatically a raised exception.

The scoped executor's existing correspondence preserves ordered occurrences.
These theorems concern that abstract protocol, not native implementation
adequacy, progress, or the decision of arbitrary propositions by non-perception.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.TypedFailure

open ScopedOutcome

inductive Kind where
  | invalidArgument | missingResource | launch | host | capacity
  | cancelled | timedOut | incompleteCapture
  deriving DecidableEq, Repr

inductive Class where
  | input | resource | operational | interruption | any
  deriving DecidableEq, Repr

/-- Membership is this vocabulary's explicit policy, not an intrinsic or
universal hierarchy of failures. Other observers may select other classes. -/
def belongs : Class → Kind → Bool
  | .any, _ => true
  | .input, .invalidArgument => true
  | .resource, .missingResource | .resource, .capacity => true
  | .interruption, .cancelled | .interruption, .timedOut => true
  | .operational, .launch | .operational, .host
  | .operational, .incompleteCapture | .operational, .missingResource
  | .operational, .capacity | .operational, .cancelled
  | .operational, .timedOut => true
  | _, _ => false

def Included (first second : Class) : Prop :=
  ∀ kind, belongs first kind = true → belongs second kind = true

theorem included_refl (category : Class) : Included category category := by
  intro kind member
  exact member

theorem included_trans {first second third : Class}
    (left : Included first second) (right : Included second third) :
    Included first third := by
  intro kind member
  exact right kind (left kind member)

theorem interruption_operational : Included .interruption .operational := by
  intro kind member
  cases kind <;> simp_all [belongs]

theorem resource_operational : Included .resource .operational := by
  intro kind member
  cases kind <;> simp_all [belongs]

theorem every_class_any (category : Class) : Included category .any := by
  intro kind _
  cases kind <;> rfl

universe u v
variable {Payload : Kind → Type u} {α : Type v}

structure Failure (Payload : Kind → Type u) (kind : Kind) where
  payload : Payload kind
  contexts : List String

abbrev AnyFailure (Payload : Kind → Type u) := Sigma (Failure Payload)

def addContext (context : String) (fault : AnyFailure Payload) : AnyFailure Payload :=
  ⟨fault.1, {fault.2 with contexts := context :: fault.2.contexts}⟩

theorem context_keeps_kind (context : String) (fault : AnyFailure Payload) :
    (addContext context fault).1 = fault.1 := rfl

theorem context_keeps_payload (context : String) (fault : AnyFailure Payload) :
    (addContext context fault).2.payload = fault.2.payload := rfl

def classHandler (category : Class)
    (recover : (kind : Kind) → belongs category kind = true →
      Failure Payload kind → Outcome α (AnyFailure Payload)) :
    Handler α (AnyFailure Payload) := fun fault =>
  if member : belongs category fault.1 = true then
    some (recover fault.1 member fault.2)
  else some (.raised fault)

theorem handle_data (category : Class)
    (recover : (kind : Kind) → belongs category kind = true →
      Failure Payload kind → Outcome α (AnyFailure Payload)) (value : α) :
    handleOne (classHandler category recover) (.value value) = some (.value value) := rfl

theorem handle_other (category : Class)
    (recover : (kind : Kind) → belongs category kind = true →
      Failure Payload kind → Outcome α (AnyFailure Payload))
    (fault : AnyFailure Payload) (outside : belongs category fault.1 ≠ true) :
    handleOne (classHandler category recover) (.raised fault) = some (.raised fault) := by
  simp [handleOne, classHandler, outside]

theorem handle_member (category : Class)
    (recover : (kind : Kind) → belongs category kind = true →
      Failure Payload kind → Outcome α (AnyFailure Payload))
    (fault : AnyFailure Payload) (inside : belongs category fault.1 = true) :
    handleOne (classHandler category recover) (.raised fault) =
      some (recover fault.1 inside fault.2) := by
  simp [handleOne, classHandler, inside]

theorem typed_handlers_preserve_occurrences
    (program : Computation α (AnyFailure Payload))
    (handlers : List (Handler α (AnyFailure Payload))) :
    execute handlers program = (denote program).filterMap (route handlers) :=
  execute_eq_denote program handlers

inductive FrontierStop (Reason : Type u) where
  | exhausted
  | unfinished (reason : Reason)
  deriving DecidableEq

structure Frontier (α : Type v) (ε Reason : Type u) where
  occurrences : List (Outcome α ε)
  stop : FrontierStop Reason

/-- Positive absence requires both producer exhaustion and no occurrences,
not merely a temporarily empty buffer. -/
def ClosedZero {ε Reason : Type u} (frontier : Frontier α ε Reason) : Prop :=
  frontier.occurrences = [] ∧ frontier.stop = .exhausted

theorem unfinished_not_closed_zero {ε Reason : Type u}
    (occurrences : List (Outcome α ε)) (reason : Reason) :
    ¬ ClosedZero (Frontier.mk occurrences (.unfinished reason)) := by
  simp [ClosedZero]

theorem data_not_closed_zero {ε Reason : Type u} (value : α)
    (tail : List (Outcome α ε)) (stop : FrontierStop Reason) :
    ¬ ClosedZero (Frontier.mk (.value value :: tail) stop) := by
  simp [ClosedZero]

theorem fault_not_closed_zero {ε Reason : Type u} (fault : ε)
    (tail : List (Outcome α ε)) (stop : FrontierStop Reason) :
    ¬ ClosedZero (Frontier.mk (.raised fault :: tail) stop) := by
  simp [ClosedZero]

theorem closed_zero_licenses_empty_completion {α ε Reason : Type}
    (frontier : Frontier α ε Reason) (closed : ClosedZero frontier) :
    frontier = ⟨[], .exhausted⟩ ∧
    Completion.ObservationComplete (State := Reason) (Fault := ε)
      Completion.Demand.exhaustive frontier.occurrences
      (.observed .complete) := by
  constructor
  · cases frontier with
    | mk occurrences stop => simp_all [ClosedZero]
  · exact Completion.ObservationComplete.exhaustive frontier.occurrences

example : belongs .interruption .cancelled = true := rfl
example : belongs .operational .missingResource = true := rfl
example : belongs .interruption .invalidArgument = false := rfl
example : ¬ Included .any .interruption := by
  intro inclusion
  have impossible := inclusion .invalidArgument rfl
  cases impossible

end Mettapedia.Machines.RunContracts.TypedFailure
