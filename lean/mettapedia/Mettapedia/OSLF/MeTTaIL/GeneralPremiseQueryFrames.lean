import Mettapedia.OSLF.MeTTaIL.GeneralPremiseScheduler
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-!
# Retained typed frames for structural relation queries

The machine scans one provider row, query argument or matcher transition at a
time. A matcher answer has its own cursor, so pausing during an alternative
cannot discard it. Provider-row positions and structural bag choices retain
separate occurrence origins. Proof fields certify the independent query
judgment and are erased by compilation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Request where
  context : Context
  relation : String
  arguments : List Pattern
  initial : Assignment
  deriving Repr

structure Answer (environment : Environment) (request : Request) where
  rowIndex : Nat
  assignment : Assignment
  origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)
  valid : TracedQuery environment request.context request.relation request.arguments
    request.initial rowIndex assignment origins

inductive Obligation where
  | signatureUnavailable (relation : String) (arity : Nat)
  | inputUnavailable (rowIndex argumentIndex : Nat)
  | argumentShape (rowIndex argumentIndex : Nat)
  deriving Repr, DecidableEq

structure RowsFrame (environment : Environment) (request : Request) where
  signature : Signature
  signatureFound : signature? environment.provider request.relation request.arguments.length =
    some signature
  cursor : Nat

structure ArgumentsFrame (environment : Environment) (request : Request) where
  rowIndex : Nat
  index : Nat
  assignment : Assignment
  schemas : List Pattern
  values : List Pattern
  modes : List RelationArgMode
  origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)
  finish : ∀ final traces,
    TracedArgumentsHold request.context index assignment schemas values modes final traces →
    TypedAssignment environment request.context final →
    TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex final (origins ++ traces)

structure MatcherFrame (environment : Environment) (request : Request) where
  rowIndex : Nat
  argumentIndex : Nat
  schemas : List Pattern
  values : List Pattern
  modes : List RelationArgMode
  origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)
  query : GeneralScopedMatchMachine.Request
  state : GeneralScopedMatchMachine.State
  reachable : GeneralScopedMatchMachine.Reachable query state
  cursor : Nat
  finish : ∀ answer,
    GeneralScopedMatchMachine.Answer.Valid query answer →
    ∀ final traces, TracedArgumentsHold request.context (argumentIndex + 1) answer.assignment
      schemas values modes final traces → TypedAssignment environment request.context final →
    TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex final ((origins ++ [(argumentIndex, answer.trace)]) ++ traces)

inductive Task (environment : Environment) (request : Request) where
  | start
  | rows (frame : RowsFrame environment request)
  | arguments (frame : ArgumentsFrame environment request)
  | matcher (frame : MatcherFrame environment request)

abbrev State (environment : Environment) (request : Request) :=
  Scheduler.State (Task environment request) (Answer environment request) Obligation


end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
