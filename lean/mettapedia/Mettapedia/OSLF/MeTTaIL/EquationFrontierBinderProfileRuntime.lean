import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileExecution

/-!
# Complete runtime outcomes for guarded binder extrusion

These laws calculate whole interpreter outcomes over every ambient-indexed
carrier and every finite provider snapshot, including repeated provider rows.
They retain captures, ordered successful query positions and exact targets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open Syntax Engine RuleBinding ScopedRuleMatching
open ScopedEquationExecution (Orientation orientedRule)
open Mettapedia.GSLT.LanguageDef.WellSorted
open ConditionalEquationExecution

@[simp] theorem ambientContext_length (ambient : Nat) :
    (ambientContext ambient).length = ambient := by simp [ambientContext]

def expectedReceipt (ambient : Nat) (index : Fin (ambient + 1)) (token : Token)
    (targetPhase : Phase) (resultIndex : Nat) : Receipt where
  matchIndex := 0
  captured := EquationFrontierBinderProfile.captured ambient index token
  completed := EquationFrontierBinderProfile.captured ambient index token
  history := [ScopedPremiseExecution.PremiseEvent.root 0 resultIndex]
  target := (⟨targetPhase, index, token⟩ : State ambient).pattern

def expectedReceipts (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (targetPhase : Phase) : List Receipt :=
  (allowed.filter (fun key => key == token)).zipIdx.map fun row =>
    expectedReceipt ambient index token targetPhase row.2

private theorem extrusion_typed_query_results (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (orientation : Orientation) :
    typedQueryResults (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) (orientedRule extrusionEquation orientation)
      (extrusionSpec orientation) 0 "allow" [.fvar "Q"] (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (ScopedPremiseExecution.PremiseEvent.root 0 entry.2,
            captured ambient index token) := by
  simp only [typedQueryResults, List.all_cons, queryArgumentSupported, List.all_nil,
    Bool.and_self, if_true, ambientContext_length]
  rw [extrusion_query_results]
  rw [List.filter_map]
  have assigned := captured_checked_extrusion ambient index token orientation
  change checkAssignment language FreeTypeContext.empty (ambientContext ambient)
    (orientedRule extrusionEquation orientation) (extrusionSpec orientation)
    (captured ambient index token) = true at assigned
  simp [Function.comp_def, assigned]

private theorem consume_typed_query_results (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    typedQueryResults (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) consumeRule consumeSpec 0 "allow" [.fvar "Q"]
      (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (ScopedPremiseExecution.PremiseEvent.root 0 entry.2,
            captured ambient index token) := by
  simp only [typedQueryResults, List.all_cons, queryArgumentSupported, List.all_nil,
    Bool.and_self, if_true, ambientContext_length]
  rw [consume_query_results]
  rw [List.filter_map]
  have assigned := captured_checked_consume ambient index token
  change checkAssignment language FreeTypeContext.empty (ambientContext ambient)
    consumeRule consumeSpec (captured ambient index token) = true at assigned
  simp [Function.comp_def, assigned]

theorem extrusion_run_queries (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (orientation : Orientation) :
    runQueries (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      (orientedRule extrusionEquation orientation) (extrusionSpec orientation)
      0 [.relationQuery "allow" [.fvar "Q"]] (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (captured ambient index token,
            [ScopedPremiseExecution.PremiseEvent.root 0 entry.2]) := by
  simp only [runQueries, extrusion_typed_query_results]
  simp only [List.map_cons, List.map_nil]
  rw [List.flatMap_map, ← List.map_eq_flatMap]

theorem consume_run_queries (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    runQueries (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      consumeRule consumeSpec 0 [.relationQuery "allow" [.fvar "Q"]]
      (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (captured ambient index token,
            [ScopedPremiseExecution.PremiseEvent.root 0 entry.2]) := by
  simp only [runQueries, consume_typed_query_results]
  simp only [List.map_cons, List.map_nil]
  rw [List.flatMap_map, ← List.map_eq_flatMap]

private theorem extrusion_premises (orientation : Orientation) :
    (orientedRule extrusionEquation orientation).premises =
      [.relationQuery "allow" [.fvar "Q"]] := by cases orientation <;> rfl

private theorem consume_premises : consumeRule.premises =
    [.relationQuery "allow" [.fvar "Q"]] := rfl

private theorem extrusion_declared (orientation : Orientation) :
    (orientedRule extrusionEquation orientation).bindings = some (extrusionSpec orientation) := by
  cases orientation <;> rfl

private theorem consume_declared : consumeRule.bindings = some consumeSpec := rfl

theorem extrusion_pending_empty (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (orientation : Orientation) :
    queryPending (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      (orientedRule extrusionEquation orientation) (extrusionSpec orientation) 0
      [.relationQuery "allow" [.fvar "Q"]] (captured ambient index token) = [] := by
  have support : ScopedPremiseExecution.hasOccurrenceAt (extrusionSpec orientation) 0 = false := by
    cases orientation <;> decide +kernel
  simp [queryPending, support, queryArgumentSupported, Pattern.freeFvarNames,
    List.eraseDups_cons,
    query_projection]

theorem consume_pending_empty (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    queryPending (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      consumeRule consumeSpec 0 [.relationQuery "allow" [.fvar "Q"]]
      (captured ambient index token) = [] := by
  have support : ScopedPremiseExecution.hasOccurrenceAt consumeSpec 0 = false := by
    decide +kernel
  simp [queryPending, support, queryArgumentSupported, Pattern.freeFvarNames,
    List.eraseDups_cons,
    query_projection]

private theorem extrusion_declaration_pending (orientation : Orientation) :
    declarationPending (orientedRule extrusionEquation orientation)
      (extrusionSpec orientation) = [] := by cases orientation <;> decide +kernel

private theorem consume_declaration_pending : declarationPending consumeRule consumeSpec = [] := by
  decide +kernel

theorem consume_outcome (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc consumeRule
      (⟨.exposed, index, token⟩ : State ambient).pattern =
        ⟨expectedReceipts allowed ambient index token .finished, []⟩ := by
  have sourceChecked := state_open_checked (⟨.exposed, index, token⟩ : State ambient)
  have targetChecked := state_open_checked (⟨.finished, index, token⟩ : State ambient)
  have matched := match_consume ambient index token
  change matchRuleAt consumeRule consumeSpec ambient
    (⟨.exposed, index, token⟩ : State ambient).pattern = [captured ambient index token] at matched
  have assigned := captured_checked_consume ambient index token
  change checkAssignment language FreeTypeContext.empty (ambientContext ambient)
    consumeRule consumeSpec (captured ambient index token) = true at assigned
  have reduct := reduct_consume ambient index token
  change reduct? consumeRule consumeSpec ambient (captured ambient index token) =
    some (⟨.finished, index, token⟩ : State ambient).pattern at reduct
  have admitted : admittedFor consumeRule consumeSpec = true := consume_admitted
  simp only [applyRuleAtOutcome, sourceChecked, if_true, consume_declared,
    admitted, ambientContext_length]
  simp only [receiptsFor, ambientContext_length, matched, List.zipIdx_cons, List.zipIdx_nil,
    List.flatMap_cons, List.flatMap_nil, assigned, if_true, consume_premises,
    consume_run_queries, consume_declaration_pending, consume_pending_empty,
    List.append_nil]
  simp [finishTyped?, reduct, targetChecked, expectedReceipts, expectedReceipt]

def equationSourcePhase : Orientation → Phase
  | .forward => .tucked
  | .reverse => .exposed

def equationTargetPhase : Orientation → Phase
  | .forward => .exposed
  | .reverse => .tucked

theorem extrusion_outcome (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (orientation : Orientation) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc (orientedRule extrusionEquation orientation)
      (⟨equationSourcePhase orientation, index, token⟩ : State ambient).pattern =
        ⟨expectedReceipts allowed ambient index token (equationTargetPhase orientation), []⟩ := by
  have sourceChecked := state_open_checked
    (⟨equationSourcePhase orientation, index, token⟩ : State ambient)
  have targetChecked := state_open_checked
    (⟨equationTargetPhase orientation, index, token⟩ : State ambient)
  have matched : matchRuleAt (orientedRule extrusionEquation orientation)
      (extrusionSpec orientation) ambient
      (⟨equationSourcePhase orientation, index, token⟩ : State ambient).pattern =
        [captured ambient index token] := by
    cases orientation
    · exact match_extrusion_forward ambient index token
    · exact match_extrusion_reverse ambient index token
  have assigned := captured_checked_extrusion ambient index token orientation
  change checkAssignment language FreeTypeContext.empty (ambientContext ambient)
    (orientedRule extrusionEquation orientation) (extrusionSpec orientation)
    (captured ambient index token) = true at assigned
  have reduct : reduct? (orientedRule extrusionEquation orientation)
      (extrusionSpec orientation) ambient (captured ambient index token) =
        some (⟨equationTargetPhase orientation, index, token⟩ : State ambient).pattern := by
    cases orientation
    · exact reduct_extrusion_forward ambient index token
    · exact reduct_extrusion_reverse ambient index token
  have admitted : admittedFor (orientedRule extrusionEquation orientation)
      (extrusionSpec orientation) = true := extrusion_admitted orientation
  simp only [applyRuleAtOutcome, sourceChecked, if_true, extrusion_declared,
    admitted, ambientContext_length]
  simp only [receiptsFor, ambientContext_length, matched, List.zipIdx_cons, List.zipIdx_nil,
    List.flatMap_cons, List.flatMap_nil, assigned, if_true, extrusion_premises,
    extrusion_run_queries, extrusion_declaration_pending, extrusion_pending_empty,
    List.append_nil]
  simp [finishTyped?, reduct, targetChecked, expectedReceipts, expectedReceipt]

theorem match_consume_family (ambient : Nat) (source : State ambient) :
    matchRuleAt consumeRule consumeSpec ambient source.pattern =
      if source.phase = .exposed then [captured ambient source.name source.key] else [] := by
  rcases source with ⟨phase, index, token⟩
  cases phase
  · simp [State.pattern, consumeSpec, consumeRule, nu, pair,
      matchRuleAt, matchRuleWithAt, matchAtWith]
  · exact match_consume ambient index token
  · simp [State.pattern, consumeSpec, consumeRule, nu, done, pair,
      matchRuleAt, matchRuleWithAt, matchAtWith]

theorem match_extrusion_family (ambient : Nat) (source : State ambient)
    (orientation : Orientation) :
    matchRuleAt (orientedRule extrusionEquation orientation) (extrusionSpec orientation)
      ambient source.pattern =
      if source.phase = equationSourcePhase orientation then
        [captured ambient source.name source.key] else [] := by
  rcases source with ⟨phase, index, token⟩
  cases orientation
  · cases phase
    · exact match_extrusion_forward ambient index token
    · simp [equationSourcePhase, State.pattern, extrusionSpec, orientedRule,
        extrusionEquation, ScopedEquationControls.extrusionEquation, nu, pair,
        matchRuleAt, matchRuleWithAt, matchAtWith]
    · simp [equationSourcePhase, State.pattern, extrusionSpec, orientedRule,
        extrusionEquation, ScopedEquationControls.extrusionEquation, nu, done, pair,
        matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith]
  · cases phase
    · simp [equationSourcePhase, State.pattern, extrusionSpec, orientedRule,
        extrusionEquation, ScopedEquationControls.extrusionEquation, nu, pair,
        matchRuleAt, matchRuleWithAt, matchAtWith]
    · exact match_extrusion_reverse ambient index token
    · simp [equationSourcePhase, State.pattern, extrusionSpec, orientedRule,
        extrusionEquation, ScopedEquationControls.extrusionEquation, nu, done, pair,
        matchRuleAt, matchRuleWithAt, matchAtWith]

private theorem no_match_outcome (allowed : List Token) (ambient : Nat)
    (source : State ambient) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : rule.bindings = some spec) (admitted : admittedFor rule spec = true)
    (noPending : declarationPending rule spec = [])
    (noMatch : matchRuleAt rule spec ambient source.pattern = []) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc rule source.pattern = ⟨[], []⟩ := by
  simp only [applyRuleAtOutcome, state_open_checked, if_true, declared, admitted,
    receiptsFor, ambientContext_length, noMatch, List.zipIdx_nil, List.flatMap_nil,
    noPending, List.append_nil]

theorem consume_outcome_family (allowed : List Token) (ambient : Nat)
    (source : State ambient) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc consumeRule source.pattern =
        ⟨if source.phase = .exposed then
          expectedReceipts allowed ambient source.name source.key .finished else [], []⟩ := by
  by_cases exposed : source.phase = .exposed
  · rcases source with ⟨phase, index, token⟩
    cases exposed
    exact consume_outcome allowed ambient index token
  · have noMatch : matchRuleAt consumeRule consumeSpec ambient source.pattern = [] := by
      simp [match_consume_family, exposed]
    simpa [exposed] using no_match_outcome allowed ambient source consumeRule consumeSpec
      consume_declared consume_admitted consume_declaration_pending noMatch

theorem extrusion_outcome_family (allowed : List Token) (ambient : Nat)
    (source : State ambient) (orientation : Orientation) :
    applyRuleAtOutcome (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc (orientedRule extrusionEquation orientation)
      source.pattern =
        ⟨if source.phase = equationSourcePhase orientation then
          expectedReceipts allowed ambient source.name source.key
            (equationTargetPhase orientation) else [], []⟩ := by
  by_cases active : source.phase = equationSourcePhase orientation
  · rcases source with ⟨phase, index, token⟩
    cases active
    simpa [equationSourcePhase] using extrusion_outcome allowed ambient index token orientation
  · have noMatch : matchRuleAt (orientedRule extrusionEquation orientation)
        (extrusionSpec orientation) ambient source.pattern = [] := by
      simp [match_extrusion_family, active]
    simpa [active] using no_match_outcome allowed ambient source
      (orientedRule extrusionEquation orientation) (extrusionSpec orientation)
      (extrusion_declared orientation) (extrusion_admitted orientation)
      (extrusion_declaration_pending orientation) noMatch

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
