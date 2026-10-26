import Mettapedia.OSLF.MeTTaIL.CanonicalTable
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseScheduler
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCursor
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination

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

/-- Matching captures draw their free names from the incoming assignment and target. -/
def MatchingExecution.PreservesFreeNames (matcher : MatchingExecution) : Prop :=
  ∀ {request trace final}, matcher.meaning.Matches request trace final →
    ∀ footprint : List String, assignmentFreeWithin footprint request.initial →
      (∀ name ∈ request.target.freeFvarNames, name ∈ footprint) →
      assignmentFreeWithin footprint final

theorem MatchingExecution.ordinary_preservesFreeNames :
    MatchingExecution.ordinary.PreservesFreeNames := by
  intro request trace final matched footprint before target
  exact GeneralScopedMatch.matched_free_within matched.matching footprint before target

theorem MatchingExecution.answer_free_within {matcher : MatchingExecution}
    (support : matcher.PreservesFreeNames) (request : GeneralScopedMatchMachine.Request)
    (state : matcher.State) (reached : matcher.Reachable request state)
    (answer : matcher.Answer) (member : answer ∈ matcher.answers state)
    (footprint : List String) (before : assignmentFreeWithin footprint request.initial)
    (target : ∀ name ∈ request.target.freeFvarNames, name ∈ footprint) :
    assignmentFreeWithin footprint (matcher.assignment answer) :=
  support (matcher.answers_sound reached member) footprint before target

#print axioms MatchingExecution.ordinary_preservesFreeNames
#print axioms MatchingExecution.answer_free_within

/-- Laws used when a retained consumer reads a matching service by publication cursor. -/
structure MatchingExecution.CursorLaws (matcher : MatchingExecution) where
  Unread : GeneralScopedMatchMachine.Request → matcher.State → Nat → matcher.Answer → Prop
  start : ∀ request answer, Unread request (matcher.start request) 0 answer ↔
    matcher.meaning.Matches request (matcher.trace answer) (matcher.assignment answer)
  split : ∀ request state cursor answer, Unread request state cursor answer ↔
    (matcher.answers state)[cursor]? = some answer ∨ Unread request state (cursor + 1) answer
  tick : ∀ {request state cursor answer}, matcher.Reachable request state →
    cursor ≤ (matcher.answers state).length → (matcher.answers state)[cursor]? = none →
    (Unread request (matcher.tick request state) cursor answer ↔ Unread request state cursor answer)
  complete : ∀ {request state cursor answer}, matcher.Reachable request state →
    matcher.complete state = true →
    (Unread request state cursor answer ↔ answer ∈ (matcher.answers state).drop cursor)
  answers_prefix : ∀ request state, matcher.answers state <+: matcher.answers (matcher.tick request state)

/-- A published answer at the cursor is an unread alternative. -/
theorem MatchingExecution.CursorLaws.unread_of_published {matcher : MatchingExecution}
    (laws : matcher.CursorLaws) (request : GeneralScopedMatchMachine.Request)
    (state : matcher.State) (cursor : Nat) (answer : matcher.Answer)
    (published : (matcher.answers state)[cursor]? = some answer) :
    laws.Unread request state cursor answer :=
  (laws.split request state cursor answer).mpr (.inl published)

/-- Completion leaves no unread alternative past the publication log. -/
theorem MatchingExecution.CursorLaws.no_unread_after_complete {matcher : MatchingExecution}
    (laws : matcher.CursorLaws) {request : GeneralScopedMatchMachine.Request}
    {state : matcher.State} (reached : matcher.Reachable request state)
    (finished : matcher.complete state = true) (answer : matcher.Answer) :
    ¬ laws.Unread request state (matcher.answers state).length answer := by
  rw [laws.complete reached finished]
  simp only [List.drop_length, List.not_mem_nil, not_false_eq_true]

/-- The ordinary scoped matcher supplies cursor laws from its independent pending-work meaning. -/
def MatchingExecution.ordinaryCursorLaws : MatchingExecution.CursorLaws .ordinary where
  Unread := GeneralScopedMatchMachine.MatcherUnread
  start := GeneralScopedMatchMachine.start_unread_iff
  split := GeneralScopedMatchMachine.unread_cursor_split
  tick := fun _ bounded missing => GeneralScopedMatchMachine.unread_tick_of_no_answer _ _ _ _ bounded missing
  complete := by
    intro request state cursor answer reached finished
    have empty : state.agenda = [] := List.isEmpty_iff.mp finished
    simp only [GeneralScopedMatchMachine.MatcherUnread, empty, List.not_mem_nil,
      false_and, exists_false, or_false]
  answers_prefix := GeneralScopedMatchMachine.tick_answers_prefix


/-- Proof-side work at a publication cursor, decreasing on either actual
operation of a retained matcher consumer. -/
structure MatchingExecution.CursorCost (matcher : MatchingExecution) where
  debt : GeneralScopedMatchMachine.Request → matcher.State → Nat → Nat
  consume : ∀ {request state cursor answer}, matcher.Reachable request state →
    (matcher.answers state)[cursor]? = some answer →
    debt request state (cursor + 1) < debt request state cursor
  tick : ∀ {request state cursor}, matcher.Reachable request state →
    (matcher.answers state)[cursor]? = none → matcher.complete state = false →
    debt request (matcher.tick request state) cursor < debt request state cursor

/-- A pending fixed point cannot satisfy a strictly decreasing cursor cost. -/
theorem MatchingExecution.CursorCost.no_pending_fixed_point {matcher : MatchingExecution}
    (cost : matcher.CursorCost) {request : GeneralScopedMatchMachine.Request}
    {state : matcher.State} {cursor : Nat}
    (reached : matcher.Reachable request state)
    (missing : (matcher.answers state)[cursor]? = none)
    (pending : matcher.complete state = false) :
    matcher.tick request state ≠ state := by
  intro fixed
  have decreases := cost.tick reached missing pending
  rw [fixed] at decreases
  exact Nat.lt_irrefl _ decreases

/-- The ordinary service's debt uses its actual scoped expansion agenda. -/
def MatchingExecution.ordinaryCursorCost : MatchingExecution.CursorCost .ordinary where
  debt := fun request state cursor =>
    (state.answers.length - cursor) +
      2 * GeneralScopedMatchMachine.agendaCost request state.agenda
  consume := by
    intro request state cursor answer _reached published
    change state.answers[cursor]? = some answer at published
    have within := (List.getElem?_eq_some_iff.mp published).1
    change (state.answers.length - (cursor + 1)) +
        2 * GeneralScopedMatchMachine.agendaCost request state.agenda <
      (state.answers.length - cursor) +
        2 * GeneralScopedMatchMachine.agendaCost request state.agenda
    omega
  tick := by
    intro request state cursor _reached missing pending
    have consumed := List.getElem?_eq_none_iff.mp missing
    have decreases := GeneralScopedMatchMachine.tick_cost (request := request) pending
    have published := GeneralScopedMatchMachine.tick_answers_length request state
    change (GeneralScopedMatchMachine.tick request state).answers.length - cursor +
        2 * GeneralScopedMatchMachine.agendaCost request
          (GeneralScopedMatchMachine.tick request state).agenda <
      (state.answers.length - cursor) +
        2 * GeneralScopedMatchMachine.agendaCost request state.agenda
    change state.answers.length ≤ cursor at consumed
    omega

/-- The actual ordinary answer record represents every semantic readout. -/
theorem MatchingExecution.ordinary_answer_representation
    (request : GeneralScopedMatchMachine.Request) (trace : List GeneralScopedMatchMachine.BagChoice)
    (final : Assignment)
    (_matched : MatchingExecution.ordinary.meaning.Matches request trace final) :
    ∃ answer : MatchingExecution.ordinary.Answer,
      MatchingExecution.ordinary.trace answer = trace ∧
      MatchingExecution.ordinary.assignment answer = final :=
  ⟨⟨final, trace⟩, rfl, rfl⟩

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


namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax ScopedRuleMatching CanonicalCompare CanonicalCompare.AllNameSupport

def MatchingExecution.PreservesNames (matcher : MatchingExecution) : Prop :=
  ∀ {request trace final}, matcher.meaning.Matches request trace final →
    ∀ table, AssignmentCovered table request.initial → Covered table request.target →
      AssignmentCovered table final

theorem MatchingExecution.ordinary_preservesNames : MatchingExecution.ordinary.PreservesNames := by
  intro request trace final matched table before target
  exact matched_covered before target matched.matching


theorem MatchingExecution.answer_covered {matcher : MatchingExecution} (support : matcher.PreservesNames)
    {request : GeneralScopedMatchMachine.Request} {state : matcher.State}
    (reachable : matcher.Reachable request state) {answer : matcher.Answer}
    (member : answer ∈ matcher.answers state) {table : List String}
    (before : AssignmentCovered table request.initial) (target : Covered table request.target) :
    AssignmentCovered table (matcher.assignment answer) :=
  support (matcher.answers_sound reachable member) table before target


end Mettapedia.OSLF.MeTTaIL.GeneralPremise

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.PreservesNames
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinary_preservesNames
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.answer_covered
