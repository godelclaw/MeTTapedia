import Mettapedia.OSLF.MeTTaIL.GeneralPremiseScheduler
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness

/-!
# Retained typed frames for structural relation queries

The machine scans one provider row, query argument or matcher transition at a
time. A matcher answer has its own cursor, so pausing during an alternative
cannot discard it. Provider-row positions and structural bag choices retain
separate occurrence origins. Proof fields certify the independent query
judgment and are erased by compilation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

/-- The matching operations used inside retained premise frames. The source
interpretation is independent of the retained state and its publication.
This is an internal service of the existing scheduler; it supplies no search
runner, explorer or admission authority. -/
structure MatchingExecution where
  Choice : Type
  meaning : MatchingInterpretation Choice
  State : Type
  Answer : Type
  assignment : Answer → Assignment
  trace : Answer → List Choice
  start : GeneralScopedMatchMachine.Request → State
  tick : GeneralScopedMatchMachine.Request → State → State
  answers : State → List Answer
  complete : State → Bool
  Reachable : GeneralScopedMatchMachine.Request → State → Prop
  start_reachable : ∀ request, Reachable request (start request)
  tick_reachable : ∀ {request state}, Reachable request state →
    Reachable request (tick request state)
  answers_sound : ∀ {request state}, Reachable request state → ∀ {answer},
    answer ∈ answers state → meaning.Matches request (trace answer) (assignment answer)
  acceptsInput : GeneralScopedMatchMachine.Request → Pattern → Bool
  input_sound : ∀ {request actual},
    instantiateAt? request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema = some actual →
    acceptsInput request actual = true → meaning.Input request
  input_complete : ∀ {request}, meaning.Input request → ∃ actual,
    instantiateAt? request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema = some actual ∧
    acceptsInput request actual = true

/-- The established matcher retains its state, answer representation and
literal input test in the shared frames. -/
abbrev MatchingExecution.ordinary : MatchingExecution where
  Choice := GeneralScopedMatchMachine.BagChoice
  meaning := ordinaryInterpretation
  State := GeneralScopedMatchMachine.State
  Answer := GeneralScopedMatchMachine.Answer
  assignment := GeneralScopedMatchMachine.Answer.assignment
  trace := GeneralScopedMatchMachine.Answer.trace
  start := GeneralScopedMatchMachine.start
  tick := GeneralScopedMatchMachine.tick
  answers := GeneralScopedMatchMachine.State.answers
  complete := GeneralScopedMatchMachine.complete
  Reachable := GeneralScopedMatchMachine.Reachable
  start_reachable := fun _ => .start
  tick_reachable := fun reached => GeneralScopedMatchMachine.reachable_tick reached
  answers_sound := fun {_ _} reached {_} member => GeneralScopedMatchMachine.answers_sound reached member
  acceptsInput := fun request actual => actual == request.target
  input_sound := by
    intro request actual read same
    simpa only [beq_iff_eq.mp same] using read
  input_complete := fun held => ⟨_, held, by simp⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Request where
  context : Context
  relation : String
  arguments : List Pattern
  initial : Assignment
  deriving Repr

structure Answer (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  rowIndex : Nat
  assignment : Assignment
  origins : List (Nat × List matcher.Choice)
  valid : Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments
    request.initial rowIndex assignment origins

inductive Obligation where
  | signatureUnavailable (relation : String) (arity : Nat)
  | inputUnavailable (rowIndex argumentIndex : Nat)
  | argumentShape (rowIndex argumentIndex : Nat)
  | dynamicInputUnavailable (argumentIndex : Nat)
  | dynamicArgumentShape (argumentIndex : Nat)
  | dynamicUnavailable (relation : String)
  deriving Repr, DecidableEq

structure RowsFrame (environment : Environment) (request : Request) where
  signature : Signature
  signatureFound : signature? environment.provider request.relation request.arguments.length =
    some signature
  cursor : Nat

structure ArgumentsFrame (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  rowIndex : Nat
  index : Nat
  assignment : Assignment
  schemas : List Pattern
  values : List Pattern
  modes : List RelationArgMode
  origins : List (Nat × List matcher.Choice)
  finish : ∀ final traces,
    Interpreted.TracedArgumentsHold matcher.meaning request.context index assignment schemas values modes final traces →
    TypedAssignment environment request.context final →
    Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments request.initial
      rowIndex final (origins ++ traces)

structure MatcherFrame (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  rowIndex : Nat
  argumentIndex : Nat
  schemas : List Pattern
  values : List Pattern
  modes : List RelationArgMode
  origins : List (Nat × List matcher.Choice)
  query : GeneralScopedMatchMachine.Request
  state : matcher.State
  reachable : matcher.Reachable query state
  cursor : Nat
  finish : ∀ answer : matcher.Answer,
    matcher.meaning.Matches query (matcher.trace answer) (matcher.assignment answer) →
    ∀ final traces, Interpreted.TracedArgumentsHold matcher.meaning request.context (argumentIndex + 1) (matcher.assignment answer)
      schemas values modes final traces → TypedAssignment environment request.context final →
    Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments request.initial
      rowIndex final ((origins ++ [(argumentIndex, matcher.trace answer)]) ++ traces)

/-- Input resolution is retained separately from row matching. The provider
receives concrete inputs and the original output schemas, never bindings from
a different query occurrence. -/
structure DynamicInputsFrame (environment : Environment) (request : Request) where
  signature : Signature
  signatureFound : signature? environment.provider request.relation request.arguments.length =
    some signature
  registered : request.relation ∈ environment.provider.dynamicRelations
  index : Nat
  schemas : List Pattern
  modes : List RelationArgMode
  resolvedRev : List Pattern
  finish : ∀ values,
    DynamicInputs request.context index request.initial schemas modes values →
    DynamicInputs request.context 0 request.initial request.arguments signature.modes
      (resolvedRev.reverse ++ values)

/-- A dynamic table is obtained once and retained while each occurrence is
matched. Its source relation is independent of the query machine. -/
structure DynamicRowsFrame (environment : Environment) (request : Request) where
  signature : Signature
  signatureFound : signature? environment.provider request.relation request.arguments.length =
    some signature
  registered : request.relation ∈ environment.provider.dynamicRelations
  resolved : List Pattern
  inputs : DynamicInputs request.context 0 request.initial request.arguments signature.modes resolved
  rows : List (List Pattern)
  source : environment.dynamic.Source request.relation resolved rows
  cursor : Nat

inductive Task (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) where
  | start
  | rows (frame : RowsFrame environment request)
  | dynamicInputs (frame : DynamicInputsFrame environment request)
  | dynamicRows (frame : DynamicRowsFrame environment request)
  | arguments (frame : ArgumentsFrame environment request matcher)
  | matcher (frame : MatcherFrame environment request matcher)

abbrev State (environment : Environment) (request : Request)
    (matcher : MatchingExecution := MatchingExecution.ordinary) :=
  Scheduler.State (Task environment request matcher) (Answer environment request matcher) Obligation


end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
