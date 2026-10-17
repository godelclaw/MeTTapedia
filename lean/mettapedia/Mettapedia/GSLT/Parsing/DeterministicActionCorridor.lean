import Mathlib.Data.List.Basic

/-!
# Complete-action deterministic corridors in a generalized parser

The checked local list contains every enabled semantic operation, including
all lexical shift occurrences and nullable reductions. Several lookahead
witnesses may authorize the same reduction operation. Such equal operations
coalesce; different operations refuse specialization.

An admitted finite corridor preserves and reflects complete executions of the
independent general operation relation. The exact returned value is retained.
This theorem neither constructs LR tables nor establishes a native table's
grammar completeness; those are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.DeterministicActionCorridor

universe u v w

def uniqueOperation {Operation : Type u} [DecidableEq Operation] : List Operation → Option Operation
  | [] => none
  | first :: rest => if rest.all (fun next => decide (next = first)) then some first else none

theorem uniqueOperation_iff {Operation : Type u} [DecidableEq Operation]
    (enabled : List Operation) (operation : Operation) :
    uniqueOperation enabled = some operation ↔
      operation ∈ enabled ∧ ∀ other ∈ enabled, other = operation := by
  cases enabled with
  | nil => simp [uniqueOperation]
  | cons first rest =>
      by_cases same : rest.all (fun next => decide (next = first)) = true
      · simp only [uniqueOperation, same, ↓reduceIte, Option.some.injEq]
        constructor
        · intro equal
          subst operation
          refine ⟨by simp, ?_⟩
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · rfl
          · exact of_decide_eq_true ((List.all_eq_true.mp same) other member)
        · rintro ⟨_, equal⟩
          exact equal first (by simp)
      · simp only [uniqueOperation, same, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro _ equal
        apply same
        apply List.all_eq_true.mpr
        intro other member
        have head := equal first (by simp)
        exact decide_eq_true (by rw [equal other (by simp [member]), head])

inductive Effect (State : Type u) (Value : Type v) where
  | advance (state : State)
  | accept (value : Value)
  | refuse

structure Machine (State : Type u) (Operation : Type v) (Value : Type w) where
  enabled : State → List Operation
  perform : State → Operation → Effect State Value

/-- The general relation can choose any enabled operation. No scheduling
order, single lookahead token or deterministic table is assumed. -/
inductive General {State : Type u} {Operation : Type v} {Value : Type w}
    (machine : Machine State Operation Value) : State → List Operation → Value → Prop where
  | accept {state operation value} : operation ∈ machine.enabled state →
      machine.perform state operation = .accept value → General machine state [operation] value
  | advance {state operation next rest value} : operation ∈ machine.enabled state →
      machine.perform state operation = .advance next → General machine next rest value →
        General machine state (operation :: rest) value

/-- A local singleton check earns specialization. No global unambiguity
assumption and no discarded conflicting branch occurs in this admission. -/
inductive Corridor {State : Type u} {Operation : Type v} {Value : Type w} [DecidableEq Operation]
    (machine : Machine State Operation Value) : State → List Operation → Value → Prop where
  | accept {state operation value} : uniqueOperation (machine.enabled state) = some operation →
      machine.perform state operation = .accept value → Corridor machine state [operation] value
  | advance {state operation next rest value} : uniqueOperation (machine.enabled state) = some operation →
      machine.perform state operation = .advance next → Corridor machine next rest value →
        Corridor machine state (operation :: rest) value

theorem corridor_general {State : Type u} {Operation : Type v} {Value : Type w}
    [DecidableEq Operation] (machine : Machine State Operation Value)
    {state : State} {operations : List Operation} {value : Value}
    (admitted : Corridor machine state operations value) : General machine state operations value := by
  induction admitted with
  | accept unique performed =>
      exact .accept ((uniqueOperation_iff _ _).mp unique).1 performed
  | advance unique performed _ following =>
      exact .advance ((uniqueOperation_iff _ _).mp unique).1 performed following

/-- All complete general executions agree with the admitted corridor,
including the entire operation sequence and exact output value. -/
theorem corridor_unique {State : Type u} {Operation : Type v} {Value : Type w}
    [DecidableEq Operation] (machine : Machine State Operation Value)
    {state : State} {operations : List Operation} {value : Value}
    (admitted : Corridor machine state operations value) :
    ∀ {otherOperations otherValue}, General machine state otherOperations otherValue →
      otherOperations = operations ∧ otherValue = value := by
  induction admitted with
  | accept unique performed =>
      intro otherOperations otherValue general
      have same := ((uniqueOperation_iff _ _).mp unique).2
      cases general with
      | accept enabled accepted =>
          have equal := same _ enabled
          subst equal
          cases Effect.accept.inj (performed.symm.trans accepted)
          exact ⟨rfl, rfl⟩
      | advance enabled advanced following =>
          have equal := same _ enabled
          subst equal
          cases performed.symm.trans advanced
  | advance unique performed _ ih =>
      intro otherOperations otherValue general
      have same := ((uniqueOperation_iff _ _).mp unique).2
      cases general with
      | accept enabled accepted =>
          have equal := same _ enabled
          subst equal
          cases performed.symm.trans accepted
      | advance enabled advanced following =>
          have equal := same _ enabled
          subst equal
          cases Effect.advance.inj (performed.symm.trans advanced)
          obtain ⟨rfl, rfl⟩ := ih following
          exact ⟨rfl, rfl⟩

theorem corridor_exact {State : Type u} {Operation : Type v} {Value : Type w}
    [DecidableEq Operation] (machine : Machine State Operation Value)
    {state : State} {operations : List Operation} {value : Value}
    (admitted : Corridor machine state operations value) (otherOperations : List Operation) (otherValue : Value) :
    General machine state otherOperations otherValue ↔ otherOperations = operations ∧ otherValue = value := by
  constructor
  · exact corridor_unique machine admitted
  · rintro ⟨rfl, rfl⟩
    exact corridor_general machine admitted

/-! ## Repeated control configurations

A native corridor may recognize a repeated configuration by a projection of
the state (for an LR corridor: the position and the state stack, without
semantic values) when that projection determines the enabled operations and
commutes with their effects. A repeat of the projection along the corridor's
own steps excludes every complete corridor execution from the start, so
returning to the general relation discards no corridor answer. -/

universe x

/-- A projection of states that determines the enabled operations and
commutes with each operation's effect; accepted values may differ. -/
structure ControlProjection {State : Type u} {Operation : Type v} {Value : Type w}
    (machine : Machine State Operation Value) (Control : Type x) where
  project : State → Control
  enabled_eq : ∀ {state other : State}, project state = project other →
    machine.enabled state = machine.enabled other
  advance_eq : ∀ {state other next : State} {operation : Operation}, project state = project other →
    machine.perform state operation = .advance next →
      ∃ otherNext, machine.perform other operation = .advance otherNext ∧ project next = project otherNext
  accept_eq : ∀ {state other : State} {operation : Operation} {value : Value}, project state = project other →
    machine.perform state operation = .accept value →
      ∃ otherValue, machine.perform other operation = .accept otherValue

/-- Admitted corridor steps that have not yet accepted. -/
inductive Steps {State : Type u} {Operation : Type v} {Value : Type w} [DecidableEq Operation]
    (machine : Machine State Operation Value) : State → List Operation → State → Prop where
  | nil (state : State) : Steps machine state [] state
  | cons {state operation next rest final} : uniqueOperation (machine.enabled state) = some operation →
      machine.perform state operation = .advance next → Steps machine next rest final →
        Steps machine state (operation :: rest) final

theorem corridor_transfer {State : Type u} {Operation : Type v} {Value : Type w} {Control : Type x}
    [DecidableEq Operation] {machine : Machine State Operation Value}
    (projection : ControlProjection machine Control)
    {state : State} {operations : List Operation} {value : Value}
    (admitted : Corridor machine state operations value) {other : State}
    (same : projection.project state = projection.project other) :
    ∃ otherValue, Corridor machine other operations otherValue := by
  induction admitted generalizing other with
  | accept unique performed =>
      obtain ⟨otherValue, accepted⟩ := projection.accept_eq same performed
      exact ⟨otherValue, .accept (by rw [← projection.enabled_eq same]; exact unique) accepted⟩
  | advance unique performed _ ih =>
      obtain ⟨otherNext, advanced, sameNext⟩ := projection.advance_eq same performed
      obtain ⟨otherValue, rest⟩ := ih sameNext
      exact ⟨otherValue, .advance (by rw [← projection.enabled_eq same]; exact unique) advanced rest⟩

theorem corridor_after_steps {State : Type u} {Operation : Type v} {Value : Type w}
    [DecidableEq Operation] {machine : Machine State Operation Value}
    {state final : State} {taken : List Operation} (steps : Steps machine state taken final) :
    ∀ {operations : List Operation} {value : Value}, Corridor machine state operations value →
      ∃ rest, operations = taken ++ rest ∧ Corridor machine final rest value := by
  induction steps with
  | nil state =>
      intro operations value admitted
      exact ⟨operations, rfl, admitted⟩
  | cons unique performed _ ih =>
      intro operations value admitted
      cases admitted with
      | accept unique' accepted =>
          rw [unique] at unique'
          cases Option.some.inj unique'
          cases performed.symm.trans accepted
      | advance unique' advanced following =>
          rw [unique] at unique'
          cases Option.some.inj unique'
          cases Effect.advance.inj (performed.symm.trans advanced)
          obtain ⟨rest, equal, final⟩ := ih following
          exact ⟨rest, by rw [equal]; rfl, final⟩

/-- A nonempty run of corridor steps that returns to an equal projection
leaves the corridor with no complete execution from its start. -/
theorem repeated_control_excludes_corridor {State : Type u} {Operation : Type v} {Value : Type w}
    {Control : Type x} [DecidableEq Operation] {machine : Machine State Operation Value}
    (projection : ControlProjection machine Control)
    {state final : State} {taken : List Operation} (steps : Steps machine state taken final)
    (nonempty : taken ≠ []) (repeated : projection.project final = projection.project state) :
    ∀ {operations : List Operation} {value : Value}, ¬ Corridor machine state operations value := by
  intro operations value admitted
  obtain ⟨rest, equal, following⟩ := corridor_after_steps steps admitted
  obtain ⟨otherValue, transferred⟩ := corridor_transfer projection following repeated
  obtain ⟨same, _⟩ := corridor_unique machine admitted (corridor_general machine transferred)
  have lengths := congrArg List.length equal
  rw [List.length_append, same] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero (by omega))

namespace Controls

theorem repeated_lookahead_witnesses_can_authorize_one_reduction :
    uniqueOperation ([7, 7, 7] : List Nat) = some 7 := by decide

theorem one_exact_shift_is_admitted : uniqueOperation ([4] : List Nat) = some 4 := by decide

theorem different_lexical_shifts_require_general_parsing :
    uniqueOperation ([4, 5] : List Nat) = none := by decide

theorem no_enabled_operation_is_not_success :
    uniqueOperation ([] : List Nat) = none := by decide

/-- A counter that only advances: its parity repeats after two steps. -/
def counter : Machine Nat Unit Nat where
  enabled _ := [()]
  perform state _ := .advance (state + 1)

def counterParity : ControlProjection counter Nat where
  project state := state % 2
  enabled_eq _ := rfl
  advance_eq {state other _ _} same performed := by
    cases performed
    have equal : state % 2 = other % 2 := same
    exact ⟨other + 1, rfl, show (state + 1) % 2 = (other + 1) % 2 by omega⟩
  accept_eq _ performed := by cases performed

theorem counter_parity_repeat_excludes_completion (operations : List Unit) (value : Nat) :
    ¬ Corridor counter 0 operations value :=
  repeated_control_excludes_corridor counterParity
    (.cons (operation := ()) rfl rfl (.cons (operation := ()) rfl rfl (.nil 2)))
    (by simp) (by decide)

/-- Two distinct control states, then acceptance: no projection repeats. -/
def handoff : Machine Bool Nat Nat where
  enabled state := if state then [0] else [1]
  perform state operation := if state ∧ operation = 0 then .advance false
    else if ¬ state ∧ operation = 1 then .accept 5 else .refuse

theorem handoff_completes : Corridor handoff true [0, 1] 5 :=
  .advance (next := false) (by decide) rfl (.accept (by decide) rfl)

theorem handoff_identity_does_not_repeat : (id false : Bool) ≠ id true := by decide

end Controls

end Mettapedia.GSLT.Parsing.DeterministicActionCorridor
