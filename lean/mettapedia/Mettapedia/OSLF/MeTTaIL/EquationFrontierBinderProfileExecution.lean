import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
import Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution

/-!
# Executing the finite guarded binder family

These comparisons use the real authored scoped matcher, relation provider,
typed assignment gate and reduct interpreter. All ambient name indices are
covered by the family lemmas; executable controls are separate instances.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open Syntax Engine RuleBinding ScopedRuleMatching
open ScopedEquationExecution (Orientation orientedRule)
open Mettapedia.GSLT.LanguageDef.WellSorted

def cellValue (ambient : Nat) (index : Fin (ambient + 1)) : ContextualValue where
  dependencies := [.name]
  ambient := ambient
  body := cell index.val

def guardValue (ambient : Nat) (token : Token) : ContextualValue where
  dependencies := []
  ambient := ambient
  body := guard token

def captured (ambient : Nat) (index : Fin (ambient + 1)) (token : Token) :
    ScopedRuleMatching.Assignment :=
  [("Q", guardValue ambient token), ("P", cellValue ambient index)]

private theorem recovery_one (ambient : Nat) :
    recoveryAssignment 1 1 ambient [0] = Pattern.bvar := by
  funext index
  by_cases inside : index < 1
  · have zero : index = 0 := by omega
    simp [recoveryAssignment, zero]
  · have recovered : 1 + (index - 1) = index := by omega
    simp [recoveryAssignment, inside, recovered]

private theorem occurrence_one :
    occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  by_cases inside : index < 1
  · have zero : index = 0 := by omega
    simp [occurrenceAssignment, zero]
  · have recovered : 1 + (index - 1) = index := by omega
    simp [occurrenceAssignment, inside, recovered]

theorem instantiate_cellValue (ambient : Nat) (index : Fin (ambient + 1)) :
    instantiateValue? (cellValue ambient index) ambient 1 [.bvar 0] =
      some (cell index.val) := by
  have scopeBound : index.val < 1 + ambient := by omega
  simp [instantiateValue?, cellValue, cell, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, scopeBound, occurrence_one,
    ContextSubstitution.substitute_id]

theorem recover_cellValue (ambient : Nat) (index : Fin (ambient + 1)) :
    recoverValue? [.name] ambient 1 [.bvar 0] (cell index.val) =
      some (cellValue ambient index) := by
  have scopeBound : index.val < 1 + ambient := by omega
  simp [recoverValue?, cell, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    scopeBound, variableSpine?, recovery_one, ContextSubstitution.substitute_id,
    instantiateValue?, occurrence_one, cellValue]

theorem instantiate_guardValue (ambient depth : Nat) (token : Token) :
    instantiateValue? (guardValue ambient token) ambient depth [] =
      some (guard token) := by
  simp [instantiateValue?, guardValue, guard, Token.pattern,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    ContextSubstitution.substitute, ContextSubstitution.substituteList]

theorem recover_guardValue (ambient depth : Nat) (token : Token) :
    recoverValue? [] ambient depth [] (guard token) =
      some (guardValue ambient token) := by
  simp [recoverValue?, guard, Token.pattern,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt, variableSpine?,
    ContextSubstitution.substitute, ContextSubstitution.substituteList,
    guardValue, instantiateValue?]

theorem extrusion_admitted (orientation : Orientation) :
    admittedFor (orientedRule extrusionEquation orientation)
      ((orientedRule extrusionEquation orientation).bindings.getD
        { dependencies := [] }) = true := by
  cases orientation <;> decide +kernel

theorem consume_admitted :
    admittedFor consumeRule
      (consumeRule.bindings.getD { dependencies := [] }) = true := by
  decide +kernel

theorem match_extrusion_forward (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    matchRuleAt (orientedRule extrusionEquation .forward)
      ((orientedRule extrusionEquation .forward).bindings.getD
        { dependencies := [] }) ambient
      (nu (pair (cell index.val) (guard token))) =
        [captured ambient index token] := by
  simp [matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith,
    captureWith?_literal, capture?, orientedRule, extrusionEquation,
    ScopedEquationControls.extrusionEquation,
    nu, pair, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recover_cellValue, recover_guardValue, captured, assign, lookup]

theorem match_extrusion_reverse (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    matchRuleAt (orientedRule extrusionEquation .reverse)
      ((orientedRule extrusionEquation .reverse).bindings.getD
        { dependencies := [] }) ambient
      (pair (nu (cell index.val)) (guard token)) =
        [captured ambient index token] := by
  simp [matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith,
    captureWith?_literal, capture?, orientedRule, extrusionEquation,
    ScopedEquationControls.extrusionEquation, ScopedEquationExecution.exchangeBindings,
    ScopedEquationExecution.exchangeOccurrence, ScopedEquationExecution.exchangeSite,
    nu, pair, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recover_cellValue, recover_guardValue, captured, assign, lookup]

theorem match_consume (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    matchRuleAt consumeRule (consumeRule.bindings.getD { dependencies := [] })
      ambient (pair (nu (cell index.val)) (guard token)) =
        [captured ambient index token] := by
  simp [matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith,
    captureWith?_literal, capture?, consumeRule,
    nu, pair, dependencies?, arguments?, occurrenceDeclared, sitePattern?,
    occurrenceAt?, recover_cellValue, recover_guardValue, captured, assign, lookup]

theorem guard_injective : Function.Injective guard := by
  intro left right equal
  simp only [guard, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equal
  exact token_pattern_injective equal

@[simp] theorem guard_eq_iff (left right : Token) : guard left = guard right ↔ left = right :=
  guard_injective.eq_iff

def rawCaptured (index : Nat) (token : Token) : Match.Bindings :=
  [("Q", guard token), ("P", cell index)]

theorem raw_match_extrusion_forward (index : Nat) (token : Token) :
    Match.matchPattern extrusionEquation.left
      (nu (pair (cell index) (guard token))) = [rawCaptured index token] := by
  simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
    nu, pair, Match.matchPattern, Match.matchArgs, Match.mergeBindings, rawCaptured]

theorem raw_match_extrusion_reverse (index : Nat) (token : Token) :
    Match.matchPattern extrusionEquation.right
      (pair (nu (cell index)) (guard token)) = [rawCaptured index token] := by
  simp [extrusionEquation, ScopedEquationControls.extrusionEquation,
    nu, pair, Match.matchPattern, Match.matchArgs, Match.mergeBindings, rawCaptured]

theorem raw_match_consume (index : Nat) (token : Token) :
    Match.matchPattern consumeRule.left
      (pair (nu (cell index)) (guard token)) = [rawCaptured index token] := by
  simp [consumeRule, nu, pair, Match.matchPattern, Match.matchArgs,
    Match.mergeBindings, rawCaptured]

theorem reduct_extrusion_forward (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    reduct? (orientedRule extrusionEquation .forward)
      ((orientedRule extrusionEquation .forward).bindings.getD { dependencies := [] })
      ambient (captured ambient index token) =
        some (pair (nu (cell index.val)) (guard token)) := by
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?,
    orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation,
    pair, nu, arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?,
    captured, lookup, instantiate_cellValue, instantiate_guardValue]

theorem reduct_extrusion_reverse (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    reduct? (orientedRule extrusionEquation .reverse)
      ((orientedRule extrusionEquation .reverse).bindings.getD { dependencies := [] })
      ambient (captured ambient index token) =
        some (nu (pair (cell index.val) (guard token))) := by
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?,
    orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation,
    ScopedEquationExecution.exchangeBindings, ScopedEquationExecution.exchangeOccurrence,
    ScopedEquationExecution.exchangeSite,
    pair, nu, arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?,
    captured, lookup, instantiate_cellValue, instantiate_guardValue]

theorem reduct_consume (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    reduct? consumeRule (consumeRule.bindings.getD { dependencies := [] })
      ambient (captured ambient index token) =
        some (nu (done (pair (cell index.val) (guard token)))) := by
  simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, consumeRule,
    pair, nu, done, arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?,
    captured, lookup, instantiate_cellValue, instantiate_guardValue]

theorem query_projection (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    FocusedRelationQueryExecution.projectNames? ambient (captured ambient index token) ["Q"] =
      some [("Q", guard token)] := by
  simp [FocusedRelationQueryExecution.projectNames?, captured, lookup,
    instantiate_guardValue]

theorem query_reconciliation (spec : RuleBindingSpec) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    extendRoot? spec ambient (captured ambient index token) [("Q", guard token)] =
      some (captured ambient index token) := by
  simp [extendRoot?, reconcileRootResult?, captured, lookup, instantiate_guardValue]

private theorem query_row_from_seed (root : Match.Bindings) (token key : Token)
    (found : root.lookup "Q" = some (guard token)) :
    matchRelationArgs root [.fvar "Q"] [guard key] =
      if key = token then [[]] else [] := by
  by_cases equal : key = token
  · subst key
    simp [matchRelationArgs, matchRelationArgument, found, Match.mergeBindings]
  · have reverse : token ≠ key := Ne.symm equal
    simp [matchRelationArgs, matchRelationArgument, found,
      Match.mergeBindings, equal, reverse]

private theorem builtin_allow (arguments : List Pattern) :
    builtinRelationTuples language "allow" arguments = [] := by
  cases arguments with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second rest =>
      cases rest <;> rfl

theorem relation_query_from_seed (allowed : List Token) (root : Match.Bindings)
    (token : Token) (found : root.lookup "Q" = some (guard token)) :
    relationQueryStep (provider allowed) language root
      "allow" [.fvar "Q"] =
        (allowed.filter (fun key => key == token)).map (fun _ => root) := by
  simp only [relationQueryStep, provider, if_true,
    builtin_allow, List.nil_append, List.flatMap_map,
    query_row_from_seed root token _ found]
  induction allowed with
  | nil => simp
  | cons key rest ih =>
    by_cases equal : key = token
    · subst key
      simpa [Match.mergeBindings] using congrArg (List.cons root) ih
    · simpa [equal] using ih

theorem relation_query_results (allowed : List Token) (index : Nat) (token : Token) :
    relationQueryStep (provider allowed) language (rawCaptured index token)
      "allow" [.fvar "Q"] =
        (allowed.filter (fun key => key == token)).map (fun _ => rawCaptured index token) :=
  relation_query_from_seed allowed (rawCaptured index token) token
    (by simp [rawCaptured, Match.Bindings.lookup])

theorem state_canonical {ambient : Nat} (state : State ambient) :
    state.pattern.hasCanonicalBinderMetadata = true := by
  cases state with
  | mk phase name key =>
    cases phase <;> simp [State.pattern, nu, pair, cell, guard,
      Token.pattern, done, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList]

theorem state_open_sorted {ambient : Nat} (state : State ambient) :
    OpenPatternWellSorted language FreeTypeContext.empty (ambientContext ambient)
      .proc state.pattern := by
  refine ⟨state_typed state, state_canonical state, state_object state, ?_⟩
  simpa [ScopeSafeAt, ambientContext] using state_scoped state

theorem state_open_checked {ambient : Nat} (state : State ambient) :
    checkOpenPatternWellSorted language FreeTypeContext.empty (ambientContext ambient)
      .proc state.pattern = true :=
  checkOpenPatternWellSorted_complete (state_open_sorted state)

private theorem cell_checked (ambient : Nat) (index : Fin (ambient + 1)) :
    checkHasType language FreeTypeContext.empty (.name :: ambientContext ambient)
      (cell index.val) .proc = true :=
  checkHasType_complete_of_object (cell_typed ambient index)
    (by simp [cell, isObjectPattern, isObjectPatternList])

private theorem guard_checked (bound : List TypeExpr) (token : Token) :
    checkHasType language FreeTypeContext.empty bound (guard token) .proc = true :=
  checkHasType_complete_of_object (guard_typed token bound)
    (by simp [guard, Token.pattern, isObjectPattern, isObjectPatternList])

theorem captured_checked_extrusion (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) (orientation : Orientation) :
    ConditionalEquationExecution.checkAssignment language FreeTypeContext.empty
      (ambientContext ambient) (orientedRule extrusionEquation orientation)
      ((orientedRule extrusionEquation orientation).bindings.getD { dependencies := [] })
      (captured ambient index token) = true := by
  cases orientation <;>
    simp only [ConditionalEquationExecution.checkAssignment]
  all_goals simp [captured, cellValue, guardValue,
      orientedRule, extrusionEquation, ScopedEquationControls.extrusionEquation,
      ScopedEquationExecution.exchangeBindings,
      dependencies?, List.lookup, ambientContext,
      guard, Token.pattern, cell,
      isObjectPattern, isObjectPatternList]
  all_goals exact ⟨by simpa [guard, Token.pattern] using
      (guard_checked (List.replicate ambient .name) token),
    by simpa [cell, ambientContext] using (cell_checked ambient index)⟩

theorem captured_checked_consume (ambient : Nat) (index : Fin (ambient + 1))
    (token : Token) :
    ConditionalEquationExecution.checkAssignment language FreeTypeContext.empty
      (ambientContext ambient) consumeRule
      (consumeRule.bindings.getD { dependencies := [] })
      (captured ambient index token) = true := by
  simp [ConditionalEquationExecution.checkAssignment, captured, cellValue, guardValue,
    consumeRule, dependencies?, List.lookup, ambientContext,
    guard, Token.pattern, cell,
    isObjectPattern, isObjectPatternList]
  exact ⟨by simpa [guard, Token.pattern] using
      (guard_checked (List.replicate ambient .name) token),
    by simpa [cell, ambientContext] using (cell_checked ambient index)⟩

def extrusionSpec (orientation : Orientation) : RuleBindingSpec :=
  (orientedRule extrusionEquation orientation).bindings.getD { dependencies := [] }

def consumeSpec : RuleBindingSpec :=
  consumeRule.bindings.getD { dependencies := [] }

theorem extrusion_query_results (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (orientation : Orientation) :
    FocusedRelationQueryExecution.queryResults (Evidence := Empty)
      (provider allowed) language (extrusionSpec orientation) ambient 0
      "allow" [.fvar "Q"] (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (ScopedPremiseExecution.PremiseEvent.root 0 entry.2,
            captured ambient index token) := by
  have support : ScopedPremiseExecution.hasOccurrenceAt (extrusionSpec orientation) 0 = false := by
    cases orientation <;> decide +kernel
  simp only [FocusedRelationQueryExecution.queryResults, support, Bool.false_eq_true,
    if_false, Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.eraseDups_cons, List.filter_nil, List.eraseDups_nil,
    query_projection]
  rw [relation_query_from_seed allowed [("Q", guard token)] token
    (by simp [Match.Bindings.lookup])]
  rw [List.zipIdx_map]
  simp [query_reconciliation]

theorem consume_query_results (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) :
    FocusedRelationQueryExecution.queryResults (Evidence := Empty)
      (provider allowed) language consumeSpec ambient 0
      "allow" [.fvar "Q"] (captured ambient index token) =
        (allowed.filter (fun key => key == token)).zipIdx.map fun entry =>
          (ScopedPremiseExecution.PremiseEvent.root 0 entry.2,
            captured ambient index token) := by
  have support : ScopedPremiseExecution.hasOccurrenceAt consumeSpec 0 = false := by
    decide +kernel
  simp only [FocusedRelationQueryExecution.queryResults, support, Bool.false_eq_true,
    if_false, Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.eraseDups_cons, List.filter_nil, List.eraseDups_nil,
    query_projection]
  rw [relation_query_from_seed allowed [("Q", guard token)] token
    (by simp [Match.Bindings.lookup])]
  rw [List.zipIdx_map]
  simp [query_reconciliation]

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
