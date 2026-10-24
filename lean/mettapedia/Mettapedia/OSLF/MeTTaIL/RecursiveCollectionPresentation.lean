import Mettapedia.OSLF.MeTTaIL.EquationalScopedReceipts
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingPresentation

/-!
# Reconstructing an ordinary source presentation from a collection receipt

The allocation history selects one presentation without repeating search.
Selected children are placed first, in schema order, so the corresponding
ordinary matcher always consumes position zero. The original allocation
history remains the occurrence identity; the zero-position trace is only its
ordinary matching evidence. Reconstruction alone does not check captures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection
open EquationalScopedMatching CollectionMatcherCompatibility
open GeneralScopedMatchMachine

mutual
/-- Ordinary selections for a presentation whose selected children come first. -/
def frontTraceAt (path : List Nat) : Pattern → List BagChoice
  | .fvar _ | .bvar _ => []
  | .apply _ schemas => frontTraceArguments false path 0 schemas
  | .lambda _ body | .multiLambda _ _ body => frontTraceAt (path ++ [0]) body
  | .subst body replacement =>
      frontTraceAt (path ++ [0]) body ++ frontTraceAt (path ++ [1]) replacement
  | .collection kind schemas _ => frontTraceArguments (kind != .vec) path 0 schemas
termination_by schema => sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def frontTraceArguments (select : Bool) (path : List Nat) (index : Nat) :
    List Pattern → List BagChoice
  | [] => []
  | schema :: schemas =>
      (if select then [⟨path ++ [index], 0⟩] else []) ++
        frontTraceAt (path ++ [index]) schema ++ frontTraceArguments select path (index + 1) schemas
termination_by schemas => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

mutual
/-- Replay allocation decisions, leaving unused events for the next child.
This returns a presentation, not a new collection search or an admission verdict. -/
def presentAt (path : List Nat) (schema target : Pattern)
    (events : List EquationalScopedReceipts.Event) :
    Option (Pattern × List EquationalScopedReceipts.Event) :=
  match schema, target with
  | .fvar _, target => some (target, events)
  | .bvar expected, .bvar actual =>
      if expected = actual then some (target, events) else none
  | .apply label schemas, .apply actual targets =>
      if label = actual then
        (presentArguments path 0 schemas targets events).map fun (presented, remaining) =>
          (.apply actual presented, remaining)
      else none
  | .lambda _ body, .lambda display targetBody =>
      (presentAt (path ++ [0]) body targetBody events).map fun (presented, remaining) =>
        (.lambda display presented, remaining)
  | .multiLambda arity _ body, .multiLambda actual display targetBody =>
      if arity = actual then
        (presentAt (path ++ [0]) body targetBody events).map fun (presented, remaining) =>
          (.multiLambda actual display presented, remaining)
      else none
  | .subst body replacement, .subst targetBody targetReplacement => do
      let (body', remaining) ← presentAt (path ++ [0]) body targetBody events
      let (replacement', remaining) ← presentAt (path ++ [1]) replacement targetReplacement remaining
      some (.subst body' replacement', remaining)
  | .collection kind schemas rest, .collection actual targets actualRest =>
      if kind = actual ∧ actualRest = none then
        if kind = .vec then
          match rest with
          | none =>
              (presentArguments path 0 schemas targets events).map fun (presented, remaining) =>
                (.collection kind presented none, remaining)
          | some _ =>
              (presentArguments path 0 schemas (targets.take schemas.length) events).map
                fun (presented, remaining) =>
                  (.collection kind (presented ++ targets.drop schemas.length) none, remaining)
        else
          match events with
          | [] => none
          | event :: remaining =>
              if event.path = path ∧ event.kind = kind ∧ event.decisions.length = schemas.length then do
                let (values, residual) ← replay (kind == .hashSet) (arrange kind targets) event.decisions
                let (presented, remaining) ← presentArguments path 0 schemas values remaining
                some (.collection kind (presented ++ arrange kind residual) none, remaining)
              else none
      else none
  | _, _ => none
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def presentArguments (path : List Nat) (index : Nat) (schemas targets : List Pattern)
    (events : List EquationalScopedReceipts.Event) :
    Option (List Pattern × List EquationalScopedReceipts.Event) :=
  match schemas, targets with
  | [], [] => some ([], events)
  | schema :: schemas, target :: targets => do
      let (head, remaining) ← presentAt (path ++ [index]) schema target events
      let (tail, remaining) ← presentArguments path (index + 1) schemas targets remaining
      some (head :: tail, remaining)
  | _, _ => none
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation
