import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution.Primitives

/-! # Tree expansion of the original general scoped matcher -/
section MatcherTree
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval GeneralScopedMatchExecution MachineProofs

attribute [local simp] a v encoded number patternValue patternsValue assignmentValue requestValue stateValue
private abbrev MatcherTree_pathValue (path : List Nat) : Atom := encoded (encodeList Term.natural path)
private abbrev MatcherTree_worksValue (works : List GeneralScopedMatchMachine.Work) : Atom := encoded (encodeList matcherWorkTerm works)
private inductive MatcherTree_TreeForm where
  | fvar | bvar | application | lambda | multiLambda | substitution | collection | other
private def MatcherTree_TreeForm.index : MatcherTree_TreeForm → Nat
  | .fvar => 0 | .bvar => 1 | .application => 2 | .lambda => 3 | .multiLambda => 4
  | .substitution => 5 | .collection => 6 | .other => 7
private def MatcherTree_schemaCases : SpaceSemantics.Cases :=
  match (equation .tree).body with
  | .expression [.symbol "case", _, .expression rows] => (readCases rows).getD []
  | _ => []
private def MatcherTree_treeBody (form : MatcherTree_TreeForm) : Atom :=
  (MatcherTree_schemaCases[form.index]?).map Prod.snd |>.getD (.symbol "LNil")
private theorem MatcherTree_schema_cases : MatcherTree_schemaCases =
    [(a "FVar" [v "name"], MatcherTree_treeBody .fvar), (a "Var" [v "expected"], MatcherTree_treeBody .bvar),
      (a "PApp" [v "label", v "patterns"], MatcherTree_treeBody .application),
      (a "PLam" [v "display", v "body"], MatcherTree_treeBody .lambda),
      (a "PMultiLam" [v "arity", v "display", v "body"], MatcherTree_treeBody .multiLambda),
      (a "PSubst" [v "body", v "replacement"], MatcherTree_treeBody .substitution),
      (a "PCollection" [v "kind", v "patterns", v "rest"], MatcherTree_treeBody .collection),
      (v "other", MatcherTree_treeBody .other)] := by rfl
private theorem MatcherTree_tree_shape : (equation .tree).body =
    a "case" [v "schema", .expression (MatcherTree_schemaCases.map fun row => .expression [row.1, row.2])] := by rfl
private def MatcherTree_treeValues (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) : List Atom :=
  [encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
    encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec), number request.ambient,
    encoded (InferenceCettaWire.AuthoredRule.siteTerm request.site), assignmentValue assignment,
    MatcherTree_pathValue path, number depth, patternValue schema, patternValue target]
private def MatcherTree_treeCaller (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) : Subst :=
  environment .tree (MatcherTree_treeValues request assignment path depth schema target)
private def MatcherTree_schemaForm : Pattern → MatcherTree_TreeForm
  | .fvar _ => .fvar | .bvar _ => .bvar | .apply .. => .application | .lambda .. => .lambda
  | .multiLambda .. => .multiLambda | .subst .. => .substitution | .collection .. => .collection
private def MatcherTree_schemaSelected (caller : Subst) : Pattern → Subst
  | .fvar name => ("name", encoded (.string name)) :: caller
  | .bvar index => ("expected", number index) :: caller
  | .apply label patterns => ("patterns", patternsValue patterns) :: ("label", encoded (.string label)) :: caller
  | .lambda display body => ("body", patternValue body) :: ("display", encoded (InferenceCettaWire.encodeBinder display)) :: caller
  | .multiLambda arity display body => ("body", patternValue body) ::
      ("display", encoded (encodeList Term.string display)) :: ("arity", number arity) :: caller
  | .subst body replacement => ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
  | .collection kind patterns rest => ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
      ("patterns", patternsValue patterns) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller

private theorem MatcherTree_schema_case_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (schema target : Pattern) (answer : Atom)
    (continued : PureReturns program
      (MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth schema target) schema)
      state (MatcherTree_treeBody (MatcherTree_schemaForm schema)) state answer) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth schema target))
      state answer := by
  let caller := MatcherTree_treeCaller request assignment path depth schema target
  apply helper_call .tree [] state _ (MatcherTree_treeValues request assignment path depth schema target) _ rfl
    (by simp only [MatcherTree_treeValues, List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [MatcherTree_tree_shape]
  apply case_returns program caller (MatcherTree_schemaSelected caller schema) state state state (v "schema")
    (patternValue schema) (MatcherTree_treeBody (MatcherTree_schemaForm schema)) answer _ MatcherTree_schemaCases (read_cases_encoded _) _ _ continued
  · simpa [caller, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, applySubst, Subst.lookup] using
      variable_returns program caller state "schema"
  · cases schema <;> simp [MatcherTree_schemaSelected, MatcherTree_schemaForm, caller, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
      Helper.names, MatcherTree_schema_cases, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder,
      InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]

private def MatcherTree_targetCases (form : MatcherTree_TreeForm) : SpaceSemantics.Cases :=
  match MatcherTree_treeBody form with
  | .expression [.symbol "case", _, .expression rows] => (readCases rows).getD []
  | _ => []
private def MatcherTree_childBody (form : MatcherTree_TreeForm) : Atom :=
  ((MatcherTree_targetCases form)[0]?).map Prod.snd |>.getD (.symbol "LNil")
private theorem MatcherTree_target_cases (form : MatcherTree_TreeForm) : MatcherTree_targetCases form = match form with
    | .bvar => [(a "Var" [v "actual"], MatcherTree_childBody .bvar), (v "other", .symbol "LNil")]
    | .application => [(a "PApp" [v "actual", v "targets"], MatcherTree_childBody .application), (v "other", .symbol "LNil")]
    | .lambda => [(a "PLam" [v "actual-display", v "actual-body"], MatcherTree_childBody .lambda), (v "other", .symbol "LNil")]
    | .multiLambda => [(a "PMultiLam" [v "actual-arity", v "actual-display", v "actual-body"], MatcherTree_childBody .multiLambda),
        (v "other", .symbol "LNil")]
    | .substitution => [(a "PSubst" [v "actual-body", v "actual-replacement"], MatcherTree_childBody .substitution), (v "other", .symbol "LNil")]
    | .collection => [(a "PCollection" [v "actual-kind", v "targets", .symbol "RNone"], MatcherTree_childBody .collection), (v "other", .symbol "LNil")]
    | _ => [] := by cases form <;> rfl
private theorem MatcherTree_target_shape (form : MatcherTree_TreeForm)
    (supported : form ≠ .fvar ∧ form ≠ .other) : MatcherTree_treeBody form =
    a "case" [v "target", .expression ((MatcherTree_targetCases form).map fun row => .expression [row.1, row.2])] := by
  cases form <;> first | rfl | simp_all
private def MatcherTree_targetNames : MatcherTree_TreeForm → List String
  | .bvar => ["actual", "other"]
  | .application => ["actual", "targets", "other"]
  | .lambda => ["actual-display", "actual-body", "other"]
  | .multiLambda => ["actual-arity", "actual-display", "actual-body", "other"]
  | .substitution => ["actual-body", "actual-replacement", "other"]
  | .collection => ["actual-kind", "targets", "other"]
  | _ => []
private def MatcherTree_targetSelected (caller : Subst) : MatcherTree_TreeForm → Pattern → Subst
  | .bvar, .bvar actual => ("actual", number actual) :: caller
  | .application, .apply actual targets => ("targets", patternsValue targets) :: ("actual", encoded (.string actual)) :: caller
  | .lambda, .lambda display body => ("actual-body", patternValue body) ::
      ("actual-display", encoded (InferenceCettaWire.encodeBinder display)) :: caller
  | .multiLambda, .multiLambda arity display body => ("actual-body", patternValue body) ::
      ("actual-display", encoded (encodeList Term.string display)) :: ("actual-arity", number arity) :: caller
  | .substitution, .subst body replacement => ("actual-replacement", patternValue replacement) :: ("actual-body", patternValue body) :: caller
  | .collection, .collection kind targets none => ("targets", patternsValue targets) ::
      ("actual-kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
  | _, target => ("other", patternValue target) :: caller
private def MatcherTree_targetCode : MatcherTree_TreeForm → Pattern → Atom
  | .bvar, .bvar _ => MatcherTree_childBody .bvar
  | .application, .apply .. => MatcherTree_childBody .application
  | .lambda, .lambda .. => MatcherTree_childBody .lambda
  | .multiLambda, .multiLambda .. => MatcherTree_childBody .multiLambda
  | .substitution, .subst .. => MatcherTree_childBody .substitution
  | .collection, .collection _ _ none => MatcherTree_childBody .collection
  | _, _ => .symbol "LNil"
private theorem MatcherTree_matchValue_variable (caller : Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue caller (v name) value = matchAtom caller (v name) value := by
  cases value <;> simp only [SpaceSemantics.matchValue]
private theorem MatcherTree_matchValue_symbol (caller : Subst) (name : String) (value : Atom) :
    SpaceSemantics.matchValue caller (.symbol name) value =
      if .symbol name = value then some caller else none :=
  SpaceSemantics.matchValue_literal (.symbol name) caller value
private theorem MatcherTree_matchValue_application (caller : Subst) (head : String) (patterns values : List Atom)
    (notCons : head ≠ "cons") :
    SpaceSemantics.matchValue caller (a head patterns) (.expression values) =
      SpaceSemantics.matchValue.matchValues caller (.symbol head :: patterns) values := by
  apply SpaceSemantics.matchValue_expression_of_not_cons
  intro first rest same
  apply notCons
  exact Atom.symbol.inj (List.cons.inj same).1
private theorem MatcherTree_lookup_cons_ne (caller : Subst) (one two : String) (value : Atom) (different : one ≠ two) :
    Subst.lookup ((one, value) :: caller) two = Subst.lookup caller two := by
  simp [Subst.lookup, different]
private theorem MatcherTree_target_case_returns (caller : Subst) (state : State) (form : MatcherTree_TreeForm)
    (target : Pattern) (answer : Atom)
    (supported : form ≠ .fvar ∧ form ≠ .other)
    (fresh : ∀ name ∈ MatcherTree_targetNames form, Subst.lookup caller name = none)
    (captured : applySubst caller (v "target") = patternValue target)
    (continued : PureReturns program (MatcherTree_targetSelected caller form target) state (MatcherTree_targetCode form target) state answer) :
    PureReturns program caller state (MatcherTree_treeBody form) state answer := by
  have evaluated : PureReturns program caller state (v "target") state (patternValue target) := by
    simpa only [captured] using variable_returns program caller state "target"
  have actualFresh : form = .bvar ∨ form = .application → Subst.lookup caller "actual" = none := by
    intro same; rcases same with rfl | rfl <;> exact fresh _ (by simp [MatcherTree_targetNames])
  have targetsFresh : form = .application ∨ form = .collection → Subst.lookup caller "targets" = none := by
    intro same; rcases same with rfl | rfl <;> exact fresh _ (by simp [MatcherTree_targetNames])
  have kindFresh : form = .collection → Subst.lookup caller "actual-kind" = none := by
    intro same; subst form; exact fresh _ (by simp [MatcherTree_targetNames])
  have displayFresh : form = .lambda ∨ form = .multiLambda → Subst.lookup caller "actual-display" = none := by
    intro same; rcases same with rfl | rfl <;> exact fresh _ (by simp [MatcherTree_targetNames])
  have bodyFresh : form = .lambda ∨ form = .multiLambda ∨ form = .substitution →
      Subst.lookup caller "actual-body" = none := by
    intro same; rcases same with rfl | rfl | rfl <;> exact fresh _ (by simp [MatcherTree_targetNames])
  have arityFresh : form = .multiLambda → Subst.lookup caller "actual-arity" = none := by
    intro same; subst form; exact fresh _ (by simp [MatcherTree_targetNames])
  have replacementFresh : form = .substitution → Subst.lookup caller "actual-replacement" = none := by
    intro same; subst form; exact fresh _ (by simp [MatcherTree_targetNames])
  have otherFresh : Subst.lookup caller "other" = none := by
    cases form with
    | fvar => exact (supported.1 rfl).elim
    | other => exact (supported.2 rfl).elim
    | _ => exact fresh _ (by simp [MatcherTree_targetNames])
  rw [MatcherTree_target_shape form supported]
  apply case_returns program caller (MatcherTree_targetSelected caller form target) state state state (v "target")
    (patternValue target) (MatcherTree_targetCode form target) answer _ (MatcherTree_targetCases form) (read_cases_encoded _) evaluated _ continued
  cases form
  all_goals first | exact (supported.1 rfl).elim | exact (supported.2 rfl).elim | skip
  all_goals
    cases target with
    | collection kind targets rest =>
        cases rest <;> simp [MatcherTree_targetSelected, MatcherTree_targetCode, MatcherTree_target_cases, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeCollectionType, InferenceCettaWire.encodeRest,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          MatcherTree_matchValue_variable, MatcherTree_matchValue_symbol, MatcherTree_matchValue_application,
          SpaceSemantics.matchValue.matchValues, matchAtom, MatcherTree_lookup_cons_ne, targetsFresh, kindFresh, otherFresh]
    | _ =>
        simp [MatcherTree_targetSelected, MatcherTree_targetCode, MatcherTree_target_cases, InferenceCettaWire.encodePattern,
          InferenceCettaWire.encodeBinder, InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, MatcherTree_matchValue_variable, MatcherTree_matchValue_symbol, MatcherTree_matchValue_application,
          SpaceSemantics.matchValue.matchValues, matchAtom, MatcherTree_lookup_cons_ne, actualFresh, targetsFresh,
          displayFresh, bodyFresh, arityFresh, replacementFresh, otherFresh]

private theorem MatcherTree_selected_target_fresh (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) :
    ∀ name ∈ MatcherTree_targetNames (MatcherTree_schemaForm schema),
      Subst.lookup (MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth schema target) schema) name = none := by
  cases schema <;> simp [MatcherTree_targetNames, MatcherTree_schemaForm, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
    environment, Helper.names, Subst.lookup]
private theorem MatcherTree_selected_target_captured (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) :
    applySubst (MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth schema target) schema)
      (v "target") = patternValue target := by
  cases schema <;> simp [MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, applySubst, Subst.lookup]

private def MatcherTree_emptyWorkResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", .symbol "LNil", .symbol "LNil"], .symbol "LNil"]
private theorem MatcherTree_empty_work_template : PureData.Template program MatcherTree_emptyWorkResult := by
  unfold MatcherTree_emptyWorkResult
  wire_template
private theorem MatcherTree_empty_work_returns (caller : Subst) (state : State) (assignment : Assignment)
    (captured : applySubst caller (v "assignment") = assignmentValue assignment) :
    PureReturns program caller state MatcherTree_emptyWorkResult state
      (MatcherTree_worksValue [{ assignment := assignment, tasks := [] }]) := by
  simpa only [MatcherTree_emptyWorkResult, MatcherTree_worksValue, matcherWorkTerm, traceTerm, encodeList,
    CettaWireAtom.encode, CettaWireAtom.encodeMany, a, v, applySubst, applySubst.applySubstList,
    ← captured] using PureData.template_return program caller state MatcherTree_emptyWorkResult MatcherTree_empty_work_template
private theorem MatcherTree_fvar_shape : MatcherTree_treeBody .fvar = a "let" [v "captured", a Helper.capture.head
    [v "rule", v "spec", v "ambient", v "site", v "path", v "depth", v "assignment", v "name", v "target"],
      a Helper.capturedWork.head [v "captured"]] := by rfl
private theorem MatcherTree_bvar_shape : MatcherTree_childBody .bvar =
    a "if" [a "==" [v "expected", v "actual"], MatcherTree_emptyWorkResult, .symbol "LNil"] := by rfl
private def MatcherTree_argumentsResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherArguments" [v "path", v "depth", number 0, v "patterns", v "targets"], .symbol "LNil"],
      .symbol "LNil"], .symbol "LNil"]
private theorem MatcherTree_arguments_template : PureData.Template program MatcherTree_argumentsResult := by
  unfold MatcherTree_argumentsResult
  wire_template
private theorem MatcherTree_application_shape : MatcherTree_childBody .application =
    a "if" [a "==" [v "label", v "actual"], MatcherTree_argumentsResult, .symbol "LNil"] := by rfl

theorem matcher_tree_fvar_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (name : String) (target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.fvar name) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.fvar name) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.fvar name) target) (.fvar name)
  let result := ScopedRuleMatching.capture? request.rule request.spec request.ambient depth request.site path assignment name target
  let final := ("captured", encoded (ScopedCapture.scopedAssignmentOptionTerm result)) :: caller
  apply MatcherTree_schema_case_returns
  change PureReturns program caller state (MatcherTree_treeBody .fvar) state _
  rw [MatcherTree_fvar_shape]
  apply named_let_returns caller state "captured" _ (encoded (ScopedCapture.scopedAssignmentOptionTerm result))
  · simp [caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
  · exact matcher_capture_captured_returns caller state request path depth assignment name target _
      (by simp [caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
        MatcherTree_pathValue, applySubst, Subst.lookup])
  · simpa only [GeneralScopedMatchMachine.expand, result, MatcherTree_worksValue] using
      matcher_captured_work_captured_returns final state result (v "captured")
        (by simp [final, applySubst, Subst.lookup])

theorem matcher_tree_bvar_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth expected : Nat) (target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.bvar expected) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.bvar expected) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.bvar expected) target) (.bvar expected)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .bvar target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.bvar expected) target)
    (MatcherTree_selected_target_captured request assignment path depth (.bvar expected) target)
  cases target with
  | bvar actual =>
      let picked := MatcherTree_targetSelected caller .bvar (.bvar actual)
      change PureReturns program picked state (MatcherTree_childBody .bvar) state _
      rw [MatcherTree_bvar_shape]
      have tested := CettaWireAtom.equality_captured_returns program picked state
        (.natural expected) (.natural actual) "expected" "actual"
        (by simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
          Helper.names, applySubst, Subst.lookup])
        (by simp [picked, MatcherTree_targetSelected, applySubst, Subst.lookup])
      simp only [Term.natural.injEq] at tested
      apply bool_if_returns picked state _ _ _ _ _ tested
      by_cases same : expected = actual
      · simp only [same, decide_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        exact MatcherTree_empty_work_returns picked state assignment (by
          simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
            environment, Helper.names, applySubst, Subst.lookup])
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        exact symbol_returns program picked state "LNil"
  | _ => exact symbol_returns program _ state "LNil"

theorem matcher_tree_application_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (label : String)
    (patterns : List Pattern) (target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.apply label patterns) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.apply label patterns) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.apply label patterns) target) (.apply label patterns)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .application target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.apply label patterns) target)
    (MatcherTree_selected_target_captured request assignment path depth (.apply label patterns) target)
  cases target with
  | apply actual targets =>
      let picked := MatcherTree_targetSelected caller .application (.apply actual targets)
      change PureReturns program picked state (MatcherTree_childBody .application) state _
      rw [MatcherTree_application_shape]
      have tested := CettaWireAtom.equality_captured_returns program picked state (.string label) (.string actual) "label" "actual"
        (by simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
          Helper.names, applySubst, Subst.lookup])
        (by simp [picked, MatcherTree_targetSelected, applySubst, Subst.lookup])
      simp only [Term.string.injEq] at tested
      apply bool_if_returns picked state _ _ _ _ _ tested
      by_cases same : label = actual
      · simp only [same, decide_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        simpa [MatcherTree_argumentsResult, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm, traceTerm,
          picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
          MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program picked state MatcherTree_argumentsResult MatcherTree_arguments_template
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        exact symbol_returns program picked state "LNil"
  | _ => exact symbol_returns program _ state "LNil"


private theorem MatcherTree_appended_path_wire (path : List Nat) (index : Nat) :
    encodeList id (path.map Term.natural ++ [Term.natural index]) =
      encodeList Term.natural (path ++ [index]) := by
  have mapped : path.map Term.natural ++ [Term.natural index] = (path ++ [index]).map Term.natural := by
    simp only [List.map_append, List.map_cons, List.map_nil]
  rw [mapped, encodeList_map]
  rfl
private theorem MatcherTree_append_path_returns (caller : Subst) (state : State) (path : List Nat) (index : Nat)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [MatcherTree_pathValue path, MatcherTree_pathValue [index]]) :
    PureReturns program caller state (a "gslt:automata:append" [one, two]) state (MatcherTree_pathValue (path ++ [index])) := by
  have captured' : [one, two].map (applySubst caller) =
      [encoded (encodeList id (path.map Term.natural)), encoded (encodeList id [Term.natural index])] := by
    simpa only [MatcherTree_pathValue, encodeList_map, Function.id_comp, encodeList, id, List.map_cons, List.map_nil] using captured
  have returned := matcher_append_captured_returns caller state (path.map Term.natural) [Term.natural index] one two
    captured'
  change PureReturns program caller state (a "gslt:automata:append" [one, two]) state
    (encoded (encodeList id (path.map Term.natural ++ [Term.natural index]))) at returned
  simpa only [MatcherTree_pathValue, MatcherTree_appended_path_wire] using returned
private def MatcherTree_lambdaResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherTree" [v "nested", v "deeper", v "body", v "actual-body"], .symbol "LNil"],
      .symbol "LNil"], .symbol "LNil"]
private def MatcherTree_lambdaBody (delta : Atom) : Atom :=
  a "let*" [.expression
    [.expression [v "nested", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]],
      .expression [v "deeper", a "+" [v "depth", delta]]], MatcherTree_lambdaResult]
private theorem MatcherTree_lambda_shape : MatcherTree_childBody .lambda = MatcherTree_lambdaBody (number 1) := by rfl
private theorem MatcherTree_multi_lambda_shape : MatcherTree_childBody .multiLambda =
    a "if" [a "==" [v "arity", v "actual-arity"], MatcherTree_lambdaBody (v "arity"), .symbol "LNil"] := by rfl
private theorem MatcherTree_lambda_template : PureData.Template program MatcherTree_lambdaResult := by
  unfold MatcherTree_lambdaResult
  wire_template

theorem matcher_tree_lambda_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (display : Option String)
    (body target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.lambda display body) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.lambda display body) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.lambda display body) target) (.lambda display body)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .lambda target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.lambda display body) target)
    (MatcherTree_selected_target_captured request assignment path depth (.lambda display body) target)
  cases target with
  | lambda actualDisplay actualBody =>
      let picked := MatcherTree_targetSelected caller .lambda (.lambda actualDisplay actualBody)
      let nested := ("nested", MatcherTree_pathValue (path ++ [0])) :: picked
      let deeper := ("deeper", number (depth + 1)) :: nested
      change PureReturns program picked state (MatcherTree_childBody .lambda) state _
      rw [MatcherTree_lambda_shape]
      unfold MatcherTree_lambdaBody
      apply PureData.let_bindings_return (final := deeper)
        (pairs := [(v "nested", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
          (v "deeper", a "+" [v "depth", number 1])])
      · apply PureData.BindingsReturn.cons (bound := nested)
        · apply MatcherTree_append_path_returns picked state path 0
          simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
            MatcherTree_pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nested, picked, MatcherTree_targetSelected,
            caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := deeper)
          · apply matcher_add_returns nested state depth 1
            · simpa [nested, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                Helper.names, applySubst, Subst.lookup] using variable_returns program nested state "depth"
            · exact grounded_returns program nested state (.int 1)
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, deeper, nested, picked, MatcherTree_targetSelected,
              caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
          · exact .nil _ _
      · simpa [MatcherTree_lambdaResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm, traceTerm,
          deeper, nested, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
          Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program deeper state MatcherTree_lambdaResult MatcherTree_lambda_template
  | _ => exact symbol_returns program _ state "LNil"

theorem matcher_tree_multi_lambda_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth arity : Nat) (display : List String)
    (body target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.multiLambda arity display body) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.multiLambda arity display body) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.multiLambda arity display body) target) (.multiLambda arity display body)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .multiLambda target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.multiLambda arity display body) target)
    (MatcherTree_selected_target_captured request assignment path depth (.multiLambda arity display body) target)
  cases target with
  | multiLambda actualArity actualDisplay actualBody =>
      let picked := MatcherTree_targetSelected caller .multiLambda (.multiLambda actualArity actualDisplay actualBody)
      let nested := ("nested", MatcherTree_pathValue (path ++ [0])) :: picked
      let deeper := ("deeper", number (depth + arity)) :: nested
      change PureReturns program picked state (MatcherTree_childBody .multiLambda) state _
      rw [MatcherTree_multi_lambda_shape]
      have tested := CettaWireAtom.equality_captured_returns program picked state
        (.natural arity) (.natural actualArity) "arity" "actual-arity"
        (by simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
          Helper.names, applySubst, Subst.lookup])
        (by simp [picked, MatcherTree_targetSelected, applySubst, Subst.lookup])
      simp only [Term.natural.injEq] at tested
      apply bool_if_returns picked state _ _ _ _ _ tested
      by_cases same : arity = actualArity
      · simp only [same, decide_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        unfold MatcherTree_lambdaBody
        apply PureData.let_bindings_return (final := deeper)
          (pairs := [(v "nested", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
            (v "deeper", a "+" [v "depth", v "arity"])])
        · apply PureData.BindingsReturn.cons (bound := nested)
          · apply MatcherTree_append_path_returns picked state path 0
            simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
              MatcherTree_pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, nested, picked, MatcherTree_targetSelected,
              caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := deeper)
            · apply matcher_add_returns nested state depth arity
              · simpa [nested, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                  Helper.names, applySubst, Subst.lookup] using variable_returns program nested state "depth"
              · simpa [nested, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                  Helper.names, applySubst, Subst.lookup] using variable_returns program nested state "arity"
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, deeper, nested, picked, MatcherTree_targetSelected,
                caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
            · exact .nil _ _
        · simpa [same, MatcherTree_lambdaResult, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm, traceTerm,
            deeper, nested, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
            Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using
            PureData.template_return program deeper state MatcherTree_lambdaResult MatcherTree_lambda_template
      · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, GeneralScopedMatchMachine.expand]
        exact symbol_returns program picked state "LNil"
  | _ => exact symbol_returns program _ state "LNil"


private def MatcherTree_substitutionResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherTree" [v "body-path", v "deeper", v "body", v "actual-body"], a "LCons"
      [a "ScopedMatcherTree" [v "replacement-path", v "depth", v "replacement", v "actual-replacement"], .symbol "LNil"]],
      .symbol "LNil"], .symbol "LNil"]
private def MatcherTree_substitutionBody : Atom :=
  a "let*" [.expression
    [.expression [v "body-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]],
      .expression [v "replacement-path", a "gslt:automata:append" [v "path", a "LCons" [number 1, .symbol "LNil"]]],
      .expression [v "deeper", a "+" [v "depth", number 1]]], MatcherTree_substitutionResult]
private theorem MatcherTree_substitution_shape : MatcherTree_childBody .substitution = MatcherTree_substitutionBody := by rfl
private theorem MatcherTree_substitution_template : PureData.Template program MatcherTree_substitutionResult := by
  unfold MatcherTree_substitutionResult
  wire_template

theorem matcher_tree_substitution_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (body replacement target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.subst body replacement) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.subst body replacement) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.subst body replacement) target) (.subst body replacement)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .substitution target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.subst body replacement) target)
    (MatcherTree_selected_target_captured request assignment path depth (.subst body replacement) target)
  cases target with
  | subst actualBody actualReplacement =>
      let picked := MatcherTree_targetSelected caller .substitution (.subst actualBody actualReplacement)
      let bodyPath := ("body-path", MatcherTree_pathValue (path ++ [0])) :: picked
      let replacementPath := ("replacement-path", MatcherTree_pathValue (path ++ [1])) :: bodyPath
      let deeper := ("deeper", number (depth + 1)) :: replacementPath
      change PureReturns program picked state (MatcherTree_childBody .substitution) state _
      rw [MatcherTree_substitution_shape]
      unfold MatcherTree_substitutionBody
      apply PureData.let_bindings_return (final := deeper)
        (pairs := [(v "body-path", a "gslt:automata:append" [v "path", a "LCons" [number 0, .symbol "LNil"]]),
          (v "replacement-path", a "gslt:automata:append" [v "path", a "LCons" [number 1, .symbol "LNil"]]),
          (v "deeper", a "+" [v "depth", number 1])])
      · apply PureData.BindingsReturn.cons (bound := bodyPath)
        · apply MatcherTree_append_path_returns picked state path 0
          simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
            MatcherTree_pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup]
        · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, bodyPath, picked, MatcherTree_targetSelected,
            caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
        · apply PureData.BindingsReturn.cons (bound := replacementPath)
          · apply MatcherTree_append_path_returns bodyPath state path 1
            simp [bodyPath, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names,
              MatcherTree_pathValue, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup]
          · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, replacementPath, bodyPath, picked, MatcherTree_targetSelected,
              caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
          · apply PureData.BindingsReturn.cons (bound := deeper)
            · apply matcher_add_returns replacementPath state depth 1
              · simpa [replacementPath, bodyPath, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                  Helper.names, applySubst, Subst.lookup] using variable_returns program replacementPath state "depth"
              · exact grounded_returns program replacementPath state (.int 1)
            · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, deeper, replacementPath, bodyPath, picked, MatcherTree_targetSelected,
                caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
            · exact .nil _ _
      · simpa [MatcherTree_substitutionResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm, traceTerm,
          deeper, replacementPath, bodyPath, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
          Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.template_return program deeper state MatcherTree_substitutionResult MatcherTree_substitution_template
  | _ => exact symbol_returns program _ state "LNil"


private def MatcherTree_collectionBagResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherBag" [v "path", v "depth", number 0, v "patterns", v "rest", v "kind", v "targets"], .symbol "LNil"],
      .symbol "LNil"], .symbol "LNil"]
private def MatcherTree_vectorRestResult : Atom :=
  a "LCons" [a "ScopedMatcherWork" [v "assignment", a "LCons"
    [a "ScopedMatcherArguments" [v "path", v "depth", number 0, v "patterns", v "front"], a "LCons"
      [a "ScopedMatcherRestCapture" [v "nested", v "depth", v "name", v "kind", v "back"], .symbol "LNil"]],
      .symbol "LNil"], .symbol "LNil"]
private def MatcherTree_vectorRestNestedBody : Atom :=
  a "let" [v "nested", a "gslt:automata:append" [v "path", a "LCons" [v "length", .symbol "LNil"]], MatcherTree_vectorRestResult]
private def MatcherTree_vectorSplitCases : SpaceSemantics.Cases :=
  [(a "ScopedMatcherSplit" [v "front", v "back"], MatcherTree_vectorRestNestedBody)]
private def MatcherTree_vectorRestBody : Atom :=
  a "let" [v "length", a "gslt:automata:length" [v "patterns"], a "case"
    [a Helper.split.head [v "length", v "targets"], .expression (MatcherTree_vectorSplitCases.map fun row => .expression [row.1, row.2])]]
private def MatcherTree_vectorRestCases : SpaceSemantics.Cases :=
  [(.symbol "RNone", MatcherTree_argumentsResult), (a "RSome" [v "name"], MatcherTree_vectorRestBody)]
private theorem MatcherTree_collection_shape : MatcherTree_childBody .collection =
    a "if" [a "==" [v "kind", v "actual-kind"],
      a "if" [a "==" [v "kind", encoded (InferenceCettaWire.encodeCollectionType .vec)],
        a "case" [v "rest", .expression (MatcherTree_vectorRestCases.map fun row => .expression [row.1, row.2])],
        MatcherTree_collectionBagResult], .symbol "LNil"] := by rfl
private theorem MatcherTree_collection_bag_template : PureData.Template program MatcherTree_collectionBagResult := by
  unfold MatcherTree_collectionBagResult
  wire_template
private theorem MatcherTree_vector_rest_template : PureData.Template program MatcherTree_vectorRestResult := by
  unfold MatcherTree_vectorRestResult
  wire_template
private theorem MatcherTree_kind_wire_eq (one two : CollType) :
    InferenceCettaWire.encodeCollectionType one = InferenceCettaWire.encodeCollectionType two ↔ one = two := by
  cases one <;> cases two <;> decide +kernel
private theorem MatcherTree_split_patterns_returns (caller : Subst) (state : State) (count : Nat) (patterns : List Pattern)
    (one two : Atom) (captured : [one, two].map (applySubst caller) = [number count, patternsValue patterns]) :
    PureReturns program caller state (a Helper.split.head [one, two]) state
      (a "ScopedMatcherSplit" [patternsValue (patterns.take count), patternsValue (patterns.drop count)]) := by
  have captured' : [one, two].map (applySubst caller) =
      [number count, encoded (encodeList id (patterns.map InferenceCettaWire.encodePattern))] := by
    simpa only [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map, Function.id_comp] using captured
  have returned := matcher_split_captured_returns caller state count (patterns.map InferenceCettaWire.encodePattern) one two captured'
  change PureReturns program caller state (a Helper.split.head [one, two]) state
    (a "ScopedMatcherSplit" [encoded (encodeList id ((patterns.map InferenceCettaWire.encodePattern).take count)),
      encoded (encodeList id ((patterns.map InferenceCettaWire.encodePattern).drop count))]) at returned
  rw [← List.map_take, ← List.map_drop] at returned
  simpa only [patternsValue, InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map, Function.id_comp] using returned

theorem matcher_tree_collection_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (kind : CollType)
    (patterns : List Pattern) (rest : Option String) (target : Pattern) :
    PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth (.collection kind patterns rest) target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth (.collection kind patterns rest) target))) := by
  let caller := MatcherTree_schemaSelected (MatcherTree_treeCaller request assignment path depth (.collection kind patterns rest) target) (.collection kind patterns rest)
  apply MatcherTree_schema_case_returns
  apply MatcherTree_target_case_returns caller state .collection target _
    (by constructor <;> intro impossible <;> cases impossible)
    (MatcherTree_selected_target_fresh request assignment path depth (.collection kind patterns rest) target)
    (MatcherTree_selected_target_captured request assignment path depth (.collection kind patterns rest) target)
  cases target with
  | collection actualKind targets actualRest =>
      cases actualRest with
      | some name =>
          simpa [MatcherTree_targetCode, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, encodeList, CettaWireAtom.encode] using
            symbol_returns program (MatcherTree_targetSelected caller .collection (.collection actualKind targets (some name))) state "LNil"
      | none =>
          let picked := MatcherTree_targetSelected caller .collection (.collection actualKind targets none)
          change PureReturns program picked state (MatcherTree_childBody .collection) state _
          rw [MatcherTree_collection_shape]
          have tested := CettaWireAtom.equality_captured_returns program picked state
            (InferenceCettaWire.encodeCollectionType kind) (InferenceCettaWire.encodeCollectionType actualKind) "kind" "actual-kind"
            (by simp [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
              Helper.names, applySubst, Subst.lookup])
            (by simp [picked, MatcherTree_targetSelected, applySubst, Subst.lookup])
          simp only [MatcherTree_kind_wire_eq] at tested
          apply bool_if_returns picked state _ _ _ _ _ tested
          by_cases same : kind = actualKind
          · have selectedTrue : decide (kind = actualKind) = true := by simp [same]
            simp only [selectedTrue, ↓reduceIte]
            have testedVector := CettaWireAtom.equality_evaluated_returns program picked state
              (InferenceCettaWire.encodeCollectionType kind) (InferenceCettaWire.encodeCollectionType .vec)
              (v "kind") (encoded (InferenceCettaWire.encodeCollectionType .vec))
              (by decide +kernel) (by decide +kernel)
              (by simpa [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                Helper.names, applySubst, Subst.lookup] using variable_returns program picked state "kind")
              (grounded_returns program picked state (.string "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec"))
            simp only [MatcherTree_kind_wire_eq] at testedVector
            apply bool_if_returns picked state _ _ _ _ _ testedVector
            cases kind with
            | vec =>
                simp only [decide_true, ↓reduceIte]
                cases rest with
                | none =>
                    apply case_returns program picked picked state state state (v "rest") (.symbol "RNone")
                      MatcherTree_argumentsResult _ _ MatcherTree_vectorRestCases (read_cases_encoded _)
                    · simpa [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                        Helper.names, applySubst, Subst.lookup, InferenceCettaWire.encodeRest, CettaWireAtom.encode] using
                        variable_returns program picked state "rest"
                    · simp [MatcherTree_vectorRestCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                    · simpa [← same, MatcherTree_argumentsResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm,
                        traceTerm, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                        Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
                        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                        PureData.template_return program picked state MatcherTree_argumentsResult MatcherTree_arguments_template
                | some name =>
                    let named := ("name", encoded (.string name)) :: picked
                    let lengthBound := ("length", number patterns.length) :: named
                    let splitBound := ("back", patternsValue (targets.drop patterns.length)) ::
                      ("front", patternsValue (targets.take patterns.length)) :: lengthBound
                    let nested := ("nested", MatcherTree_pathValue (path ++ [patterns.length])) :: splitBound
                    apply case_returns program picked named state state state (v "rest") (encoded (InferenceCettaWire.encodeRest (some name)))
                      MatcherTree_vectorRestBody _ _ MatcherTree_vectorRestCases (read_cases_encoded _)
                    · simpa [picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                        Helper.names, applySubst, Subst.lookup] using variable_returns program picked state "rest"
                    · simp [MatcherTree_vectorRestCases, InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                        matchAtom, named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
                        environment, Helper.names, Subst.lookup]
                    · unfold MatcherTree_vectorRestBody
                      apply named_let_returns named state "length" _ (number patterns.length)
                      · simp [named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
                          environment, Helper.names, Subst.lookup]
                      · have computed := matcher_length_captured_returns named state
                          (patterns.map InferenceCettaWire.encodePattern) (v "patterns")
                          (by simp [named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
                            environment, Helper.names, applySubst, Subst.lookup,
                            InferenceCettaWire.encodePatterns_eq_encodeList, encodeList_map])
                        simpa only [List.length_map] using computed
                      · apply case_returns program lengthBound splitBound state state state
                          (a Helper.split.head [v "length", v "targets"])
                          (a "ScopedMatcherSplit" [patternsValue (targets.take patterns.length), patternsValue (targets.drop patterns.length)])
                          MatcherTree_vectorRestNestedBody _ _ MatcherTree_vectorSplitCases (read_cases_encoded _)
                        · apply MatcherTree_split_patterns_returns lengthBound state patterns.length targets
                          simp [lengthBound, named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
                            environment, Helper.names, applySubst, Subst.lookup]
                        · simp [MatcherTree_vectorSplitCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, splitBound, lengthBound, named,
                            picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues,
                            environment, Helper.names, Subst.lookup]
                        · unfold MatcherTree_vectorRestNestedBody
                          apply named_let_returns splitBound state "nested" _ (MatcherTree_pathValue (path ++ [patterns.length]))
                          · simp [splitBound, lengthBound, named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller,
                              MatcherTree_treeValues, environment, Helper.names, Subst.lookup]
                          · apply MatcherTree_append_path_returns splitBound state path patterns.length
                            simp [splitBound, lengthBound, named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller,
                              MatcherTree_treeValues, environment, Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList,
                              Subst.lookup, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                          · simpa [← same, MatcherTree_vectorRestResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm,
                              traceTerm, nested, splitBound, lengthBound, named, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected,
                              MatcherTree_treeCaller, MatcherTree_treeValues, environment, Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList,
                              Subst.lookup, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                              PureData.template_return program nested state MatcherTree_vectorRestResult MatcherTree_vector_rest_template
            | hashBag =>
                simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
                simpa [← same, MatcherTree_collectionBagResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm,
                  traceTerm, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                  Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program picked state MatcherTree_collectionBagResult MatcherTree_collection_bag_template
            | hashSet =>
                simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
                simpa [← same, MatcherTree_collectionBagResult, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, matcherWorkTerm, matcherTaskTerm,
                  traceTerm, picked, MatcherTree_targetSelected, caller, MatcherTree_schemaSelected, MatcherTree_treeCaller, MatcherTree_treeValues, environment,
                  Helper.names, MatcherTree_pathValue, applySubst, applySubst.applySubstList, Subst.lookup, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany] using
                  PureData.template_return program picked state MatcherTree_collectionBagResult MatcherTree_collection_bag_template
          · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
            simpa [same, GeneralScopedMatchMachine.expand, MatcherTree_worksValue, encodeList, CettaWireAtom.encode] using
              symbol_returns program picked state "LNil"
  | _ => exact symbol_returns program _ state "LNil"


def matcherExpandTreeTerm (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) : Term :=
  .application Helper.tree.head [InferenceCettaWire.AuthoredRule.rewriteTerm request.rule,
    InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec, .natural request.ambient,
    InferenceCettaWire.AuthoredRule.siteTerm request.site, ScopedCapture.scopedAssignmentTerm assignment,
    encodeList Term.natural path, .natural depth, InferenceCettaWire.encodePattern schema,
    InferenceCettaWire.encodePattern target]

theorem matcher_expand_tree_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (assignment : Assignment) (path : List Nat) (depth : Nat) (schema target : Pattern) :
    PureReturns program [] state (encoded (matcherExpandTreeTerm request assignment path depth schema target))
      state (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth schema target))) := by
  change PureReturns program [] state (a Helper.tree.head (MatcherTree_treeValues request assignment path depth schema target)) state _
  cases schema with
  | fvar name => exact matcher_tree_fvar_returns state request assignment path depth name target
  | bvar index => exact matcher_tree_bvar_returns state request assignment path depth index target
  | apply label patterns => exact matcher_tree_application_returns state request assignment path depth label patterns target
  | lambda display body => exact matcher_tree_lambda_returns state request assignment path depth display body target
  | multiLambda arity display body => exact matcher_tree_multi_lambda_returns state request assignment path depth arity display body target
  | subst body replacement => exact matcher_tree_substitution_returns state request assignment path depth body replacement target
  | collection kind patterns rest => exact matcher_tree_collection_returns state request assignment path depth kind patterns rest target

theorem matcher_expand_tree_captured_returns (caller : Subst) (state : State)
    (request : GeneralScopedMatchMachine.Request) (assignment : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = MatcherTree_treeValues request assignment path depth schema target) :
    PureReturns program caller state (a Helper.tree.head arguments) state
      (MatcherTree_worksValue (GeneralScopedMatchMachine.expand request assignment (.tree path depth schema target))) :=
  helper_capture .tree caller state arguments (MatcherTree_treeValues request assignment path depth schema target) _ rfl captured
    (matcher_expand_tree_returns state request assignment path depth schema target)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution.GeneralExecution
end MatcherTree
