import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderContextualExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseLocal

/-!
# Canonical pattern operations for authored premises

The shared rule program computes syntactic free-variable occurrences and
freshness over the existing full pattern wire. Binder display names and
collection rest metadata are retained as data and have exactly the existing
`Substitution.freeVars` interpretation. The first-order freshness premise
operation then composes shared binding lookup and RHS instantiation.

The lexical operations below realize the typed premise machine's parameter
shadowing, restoration and finite collection reading. These operations reuse
the loaded rule program. The typed premise machine retains ownership of
quantified bodies, ordered guards and scoped child firing.

Constructor-parameter operations realize the declaration-derived parameter
type and binder representation checks. Whole-pattern sorting belongs to the
existing `WellSortedChecker`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Equation)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval
open scoped ProgramQuotation

abbrev program : Program := RuleExecutionProgram.program

def equations (head : String) : List SpaceSemantics.Equation :=
  program.equations.filter (fun equation => equation.head == head)

theorem no_initializers : RuleExecutionProgram.premiseSource.program.initializers = [] := by
  decide +kernel

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev namesValue (names : List String) : Atom := encoded (RelationPremiseExecution.namesTerm names)
private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (MatchAutomataBindingExecution.bindingsTerm bindings)

attribute [local simp] a v encoded patternValue patternsValue namesValue bindingsValue

private inductive UnaryHelper where
  | pattern | patterns | objectPattern | objectPatterns | canonicalPattern | canonicalPatterns
private def UnaryHelper.head : UnaryHelper → String
  | .pattern => "gslt:premise:free-vars"
  | .patterns => "gslt:premise:free-vars-list"
  | .objectPattern => "gslt:premise:object-pattern"
  | .objectPatterns => "gslt:premise:object-patterns"
  | .canonicalPattern => "gslt:premise:canonical-binders"
  | .canonicalPatterns => "gslt:premise:canonical-binders-list"
private def UnaryHelper.formal : UnaryHelper → String
  | .pattern | .objectPattern | .canonicalPattern => "pattern"
  | .patterns | .objectPatterns | .canonicalPatterns => "patterns"
private def unaryEquation (helper : UnaryHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def unaryEnvironment (helper : UnaryHelper) (value : Atom) : Subst := [(helper.formal, value)]

private theorem unary_clause (helper : UnaryHelper) (value : Atom) :
    clauses program helper.head [value] =
      [.evaluate (unaryEnvironment helper value) (unaryEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [unaryEquation helper] from by cases helper <;> rfl]
  have formals : (unaryEquation helper).arguments = [v helper.formal] := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, unaryEnvironment, UnaryHelper.formal,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem unary_call (helper : UnaryHelper) (caller : Subst) (state : State)
    (value input answer : Atom) (captured : applySubst caller input = value)
    (returned : PureReturns program (unaryEnvironment helper value) state
      (unaryEquation helper).body state answer) :
    PureReturns program caller state (a helper.head [input]) state answer := by
  apply PureData.raw_authored_call_return program caller (unaryEnvironment helper value) state state
    helper.head [input] (unaryEquation helper).body answer (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst index
    cases helper <;> decide +kernel
  · simpa only [List.map_cons, List.map_nil, captured] using unary_clause helper value

private theorem unary_capture (helper : UnaryHelper) (caller : Subst) (state : State)
    (value input answer : Atom) (captured : applySubst caller input = value)
    (returned : PureReturns program [] state (a helper.head [value]) state answer) :
    PureReturns program caller state (a helper.head [input]) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head [value] [input] answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst index
    cases helper <;> decide +kernel
  · simp only [List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil, captured]

private theorem append_names_captured (caller : Subst) (state : State)
    (left right : List String) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [namesValue left, namesValue right]) :
    PureReturns program caller state (a "gslt:automata:append" [v one, v two]) state
      (namesValue (left ++ right)) := by
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  simpa only [← List.map_append, namesValue, RelationPremiseExecution.namesTerm,
    MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map Term.string) (right.map Term.string) (v one) (v two)
      (by simpa only [namesValue, RelationPremiseExecution.namesTerm,
        MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map, Function.id_comp] using captured)

private def appendBody (first second : Atom) : Atom :=
  a "let*" [.expression [.expression [v "left", first], .expression [v "right", second]],
    a "gslt:automata:append" [v "left", v "right"]]

private def varsCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], .symbol "LNil"),
   (a "FVar" [v "name"], a "LCons" [v "name", .symbol "LNil"]),
   (a "PApp" [v "head", v "children"], a "gslt:premise:free-vars-list" [v "children"]),
   (a "PLam" [v "binder", v "body"], a "gslt:premise:free-vars" [v "body"]),
   (a "PMultiLam" [v "arity", v "binders", v "body"], a "gslt:premise:free-vars" [v "body"]),
   (a "PSubst" [v "body", v "replacement"],
     appendBody (a "gslt:premise:free-vars" [v "body"])
       (a "gslt:premise:free-vars" [v "replacement"])),
   (a "PCollection" [v "kind", v "elements", v "rest"], a "gslt:premise:free-vars-list" [v "elements"])]

private def varsListCons : Atom := appendBody
  (a "gslt:premise:free-vars" [v "pattern"])
  (a "gslt:premise:free-vars-list" [v "rest"])
private def varsListCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [v "pattern", v "rest"], varsListCons)]

private def flagListCons (head lists : String) : Atom :=
  a "if" [a head [v "pattern"], a lists [v "rest"], Effects.boolean false]

private def flagListCases (head lists : String) : SpaceSemantics.Cases :=
  [(.symbol "LNil", Effects.boolean true),
   (a "LCons" [v "pattern", v "rest"], flagListCons head lists),
   (v "bad", Effects.boolean false)]

private def objectCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], Effects.boolean true),
   (a "FVar" [v "name"], Effects.boolean true),
   (a "PApp" [v "label", v "arguments"], a "gslt:premise:object-patterns" [v "arguments"]),
   (a "PLam" [v "binder", v "body"], a "gslt:premise:object-pattern" [v "body"]),
   (a "PMultiLam" [v "arity", v "binders", v "body"], a "gslt:premise:object-pattern" [v "body"]),
   (a "PSubst" [v "body", v "replacement"], Effects.boolean false),
   (a "PCollection" [v "kind", v "elements", .symbol "RNone"], a "gslt:premise:object-patterns" [v "elements"]),
   (v "bad", Effects.boolean false)]

private def canonicalCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"], Effects.boolean true),
   (a "FVar" [v "name"], Effects.boolean true),
   (a "PApp" [v "label", v "arguments"], a "gslt:premise:canonical-binders-list" [v "arguments"]),
   (a "PLam" [.symbol "BNone", v "body"], a "gslt:premise:canonical-binders" [v "body"]),
   (a "PMultiLam" [v "arity", .symbol "LNil", v "body"], a "gslt:premise:canonical-binders" [v "body"]),
   (a "PSubst" [v "body", v "replacement"],
     a "if" [a "gslt:premise:canonical-binders" [v "body"],
       a "gslt:premise:canonical-binders" [v "replacement"], Effects.boolean false]),
   (a "PCollection" [v "kind", v "elements", v "rest"], a "gslt:premise:canonical-binders-list" [v "elements"]),
   (v "bad", Effects.boolean false)]

private def UnaryHelper.cases : UnaryHelper → SpaceSemantics.Cases
  | .pattern => varsCases
  | .patterns => varsListCases
  | .objectPattern => objectCases
  | .objectPatterns => flagListCases "gslt:premise:object-pattern" "gslt:premise:object-patterns"
  | .canonicalPattern => canonicalCases
  | .canonicalPatterns => flagListCases "gslt:premise:canonical-binders" "gslt:premise:canonical-binders-list"

private theorem unary_shape (helper : UnaryHelper) : (unaryEquation helper).body =
    a "case" [v helper.formal, .expression (helper.cases.map
      fun row => .expression [row.1, row.2])] := by
  cases helper <;> decide +kernel

private theorem unary_case_returns (helper : UnaryHelper) (state : State) (value : Atom)
    (selected : Subst) (body answer : Atom)
    (matched : SpaceSemantics.selectCase (unaryEnvironment helper value) value helper.cases =
      some (selected, body))
    (returned : PureReturns program selected state body state answer) :
    PureReturns program [] state (a helper.head [value]) state answer := by
  apply unary_call helper [] state value value answer
    (Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value)
  rw [unary_shape]
  apply case_returns program (unaryEnvironment helper value) selected state state state
    (v helper.formal) value body answer _ helper.cases (read_cases_encoded _) _ matched returned
  simpa [unaryEnvironment, applySubst, Subst.lookup] using
    variable_returns program (unaryEnvironment helper value) state helper.formal

private theorem append_body_returns (caller : Subst) (state : State)
    (first second : Atom) (left right : List String)
    (leftFresh : Subst.lookup caller "left" = none)
    (rightFresh : Subst.lookup caller "right" = none)
    (firstReturned : PureReturns program caller state first state (namesValue left))
    (secondReturned : PureReturns program (("left", namesValue left) :: caller)
      state second state (namesValue right)) :
    PureReturns program caller state (appendBody first second) state (namesValue (left ++ right)) := by
  apply PureData.let_bindings_return
    (pairs := [(v "left", first), (v "right", second)])
    (final := ("right", namesValue right) :: ("left", namesValue left) :: caller)
  · apply PureData.BindingsReturn.cons
      (bound := ("left", namesValue left) :: caller) firstReturned
    · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, leftFresh]
    · apply PureData.BindingsReturn.cons
        (bound := ("right", namesValue right) :: ("left", namesValue left) :: caller) secondReturned
      have extendedFresh : Subst.lookup (("left", namesValue left) :: caller) "right" = none := by
        change Subst.lookup caller "right" = none
        exact rightFresh
      · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
          extendedFresh]
      · exact .nil _ _
  · apply append_names_captured _ state left right "left" "right"
    simp [applySubst, Subst.lookup]

/-- A list traversal composes the actual source calls supplied by structural
induction on its elements. Every append remains the retained ordered append. -/
private theorem free_vars_list_from_elements (state : State) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a "gslt:premise:free-vars" [patternValue pattern]) state
      (namesValue (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern))) :
    PureReturns program [] state (a "gslt:premise:free-vars-list" [patternsValue patterns]) state
      (namesValue (patterns.flatMap Mettapedia.OSLF.MeTTaIL.Substitution.freeVars)) := by
  induction patterns with
  | nil =>
      simp only [patternsValue, namesValue, RelationPremiseExecution.namesTerm,
        encoded, InferenceCettaWire.encodePatterns, encodeList, CettaWire.encodeList,
        List.flatMap_nil, CettaWireAtom.encode]
      apply unary_case_returns .patterns state (.symbol "LNil")
        (unaryEnvironment .patterns (.symbol "LNil")) (.symbol "LNil")
      · simp [UnaryHelper.cases, varsListCases, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "LNil"
  | cons pattern patterns ih =>
      let caller := unaryEnvironment .patterns (patternsValue (pattern :: patterns))
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      have first := elements pattern (by simp)
      have rest := ih (fun child member => elements child (List.mem_cons_of_mem _ member))
      apply unary_case_returns .patterns state (patternsValue (pattern :: patterns))
        selected varsListCons
      · simp [UnaryHelper.cases, varsListCases, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply append_body_returns selected state _ _ _ _
        · simp [selected, caller, unaryEnvironment, UnaryHelper.formal, Subst.lookup]
        · simp [selected, caller, unaryEnvironment, UnaryHelper.formal, Subst.lookup]
        · apply unary_capture .pattern selected state (patternValue pattern) (v "pattern") _ _ first
          simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
        · apply unary_capture .patterns (("left", namesValue (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern)) :: selected)
            state (patternsValue patterns) (v "rest") _ _ rest
          simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]

/-- Full canonical Pattern syntax executes through the retained source scan.
This statement includes actual binders, substitutions and collection payloads,
without claiming that the first-order rule dispatcher executes those forms. -/
theorem free_vars_returns (state : State) (pattern : Pattern) :
    PureReturns program [] state (a "gslt:premise:free-vars" [patternValue pattern]) state
      (namesValue (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let caller := unaryEnvironment .pattern (patternValue (.bvar index))
      let selected := ("index", encoded (.natural index)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.bvar index)) selected (.symbol "LNil")
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact symbol_returns program selected state "LNil"
  | hfvar name =>
      let caller := unaryEnvironment .pattern (patternValue (.fvar name))
      let selected := ("name", encoded (.string name)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.fvar name)) selected
        (a "LCons" [v "name", .symbol "LNil"])
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · have returned : PureReturns program selected state (v "name") state (encoded (.string name)) := by
          simpa [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup] using
            variable_returns program selected state "name"
        simpa only [namesValue, RelationPremiseExecution.namesTerm, encodeList, encoded,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          PureData.constructor_return program selected state "LCons"
            [v "name", .symbol "LNil"] [encoded (.string name), .symbol "LNil"]
            (by decide +kernel) (by decide)
            (.cons returned (.cons (symbol_returns program selected state "LNil") .nil))
  | happly head children ih =>
      let caller := unaryEnvironment .pattern (patternValue (.apply head children))
      let selected := ("children", patternsValue children) :: ("head", encoded (.string head)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.apply head children)) selected
        (a "gslt:premise:free-vars-list" [v "children"])
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply unary_capture .patterns selected state (patternsValue children) (v "children")
          _ _ (free_vars_list_from_elements state children ih)
        simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
  | hlambda binder body ih =>
      let caller := unaryEnvironment .pattern (patternValue (.lambda binder body))
      let selected := ("body", patternValue body) :: ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.lambda binder body)) selected
        (a "gslt:premise:free-vars" [v "body"])
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply unary_capture .pattern selected state (patternValue body) (v "body") _ _ ih
        simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
  | hmultiLambda arity binders body ih =>
      let caller := unaryEnvironment .pattern (patternValue (.multiLambda arity binders body))
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) ::
        ("arity", encoded (.natural arity)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.multiLambda arity binders body)) selected
        (a "gslt:premise:free-vars" [v "body"])
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply unary_capture .pattern selected state (patternValue body) (v "body") _ _ ih
        simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
  | hsubst body replacement bodyIH replacementIH =>
      let caller := unaryEnvironment .pattern (patternValue (.subst body replacement))
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.subst body replacement)) selected
        (appendBody (a "gslt:premise:free-vars" [v "body"])
          (a "gslt:premise:free-vars" [v "replacement"]))
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply append_body_returns selected state _ _ _ _
        · simp [selected, caller, unaryEnvironment, UnaryHelper.formal, Subst.lookup]
        · simp [selected, caller, unaryEnvironment, UnaryHelper.formal, Subst.lookup]
        · apply unary_capture .pattern selected state (patternValue body) (v "body") _ _ bodyIH
          simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
        · apply unary_capture .pattern
            (("left", namesValue (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars body)) :: selected)
            state (patternValue replacement) (v "replacement") _ _ replacementIH
          simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]
  | hcollection kind elements rest ih =>
      let caller := unaryEnvironment .pattern (patternValue (.collection kind elements rest))
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) ::
        ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      apply unary_case_returns .pattern state (patternValue (.collection kind elements rest)) selected
        (a "gslt:premise:free-vars-list" [v "elements"])
      · simp [UnaryHelper.cases, varsCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply unary_capture .patterns selected state (patternsValue elements) (v "elements")
          _ _ (free_vars_list_from_elements state elements ih)
        simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]

theorem free_vars_captured_returns (caller : Subst) (state : State) (pattern : Pattern)
    (input : Atom) (captured : applySubst caller input = patternValue pattern) :
    PureReturns program caller state (a "gslt:premise:free-vars" [input]) state
      (namesValue (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern)) :=
  unary_capture .pattern caller state _ _ _ captured (free_vars_returns state pattern)

theorem free_vars_list_returns (state : State) (patterns : List Pattern) :
    PureReturns program [] state (a "gslt:premise:free-vars-list" [patternsValue patterns]) state
      (namesValue (patterns.flatMap Mettapedia.OSLF.MeTTaIL.Substitution.freeVars)) :=
  free_vars_list_from_elements state patterns (fun pattern _ => free_vars_returns state pattern)

theorem free_vars_list_captured_returns (caller : Subst) (state : State) (patterns : List Pattern)
    (input : Atom) (captured : applySubst caller input = patternsValue patterns) :
    PureReturns program caller state (a "gslt:premise:free-vars-list" [input]) state
      (namesValue (patterns.flatMap Mettapedia.OSLF.MeTTaIL.Substitution.freeVars)) :=
  unary_capture .patterns caller state _ _ _ captured (free_vars_list_returns state patterns)

private inductive BinaryHelper where | fresh | resolve
private def BinaryHelper.head : BinaryHelper → String
  | .fresh => "gslt:premise:fresh"
  | .resolve => "gslt:premise:resolve-name"
private def BinaryHelper.second : BinaryHelper → String
  | .fresh => "pattern"
  | .resolve => "bindings"
private def binaryEquation (helper : BinaryHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def binaryEnvironment (helper : BinaryHelper) (name : String) (value : Atom) : Subst :=
  [(helper.second, value), ("name", encoded (.string name))]

private theorem binary_clause (helper : BinaryHelper) (name : String) (value : Atom) :
    clauses program helper.head [encoded (.string name), value] =
      [.evaluate (binaryEnvironment helper name value) (binaryEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [binaryEquation helper] from by cases helper <;> rfl]
  have formals : (binaryEquation helper).arguments = [v "name", v helper.second] := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, binaryEnvironment, BinaryHelper.second,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem binary_call (helper : BinaryHelper) (caller : Subst) (state : State)
    (name : String) (value one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string name), value])
    (returned : PureReturns program (binaryEnvironment helper name value) state
      (binaryEquation helper).body state answer) :
    PureReturns program caller state (a helper.head [one, two]) state answer := by
  apply PureData.raw_authored_call_return program caller (binaryEnvironment helper name value) state state
    helper.head [one, two] (binaryEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact binary_clause helper name value

private theorem member_names_captured (caller : Subst) (state : State)
    (name : String) (names : List String) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [encoded (.string name), namesValue names]) :
    PureReturns program caller state (a "gslt:automata:member" [v one, v two]) state
      (Effects.boolean (names.contains name)) := by
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  have checked := PureData.raw_capture_returns MatchAutomataProgram.program [] caller state state
    "gslt:automata:member"
    [encoded (.string name), MatchAutomataSourceExecution.listValue (names.map Term.string)]
    [v one, v two] (Effects.boolean (decide (Term.string name ∈ names.map Term.string)))
    (by decide +kernel) (by
      intro index bounded
      have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
      rcases small with rfl | rfl <;> decide +kernel) (by decide)
    (by simpa only [namesValue, RelationPremiseExecution.namesTerm, MatchAutomataSourceExecution.listValue,
        encodeList_map, Function.id_comp, List.map_cons, List.map_nil,
        CettaWireAtom.applySubst_encode] using captured.symm)
    (MatchAutomataSourceExecution.member_returns state (.string name) (names.map Term.string))
  simpa [List.contains_eq_mem, List.mem_map, Term.string.injEq] using checked

private def freshBody : Atom :=
  a "let" [v "names", a "gslt:premise:free-vars" [v "pattern"],
    a "if" [a "gslt:automata:member" [v "name", v "names"], Effects.boolean false, Effects.boolean true]]

private theorem fresh_shape : (binaryEquation .fresh).body = freshBody := by decide +kernel

theorem fresh_captured_returns (caller : Subst) (state : State) (name : String) (pattern : Pattern)
    (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string name), patternValue pattern]) :
    PureReturns program caller state (a "gslt:premise:fresh" [one, two]) state
      (Effects.boolean (Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern)) := by
  let callee := binaryEnvironment .fresh name (patternValue pattern)
  let names := Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern
  let bound := ("names", namesValue names) :: callee
  apply binary_call .fresh caller state name (patternValue pattern) one two _ captured
  rw [fresh_shape]
  apply let_returns program callee bound state state state (v "names") _ _ (namesValue names) _
  · apply free_vars_captured_returns callee state pattern (v "pattern")
    simp [callee, binaryEnvironment, BinaryHelper.second, applySubst, Subst.lookup]
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, callee, binaryEnvironment, BinaryHelper.second, bound]
  · apply if_returns program bound state state state _ (Effects.boolean (names.contains name))
      (Effects.boolean false) (Effects.boolean true) _
    · apply member_names_captured bound state name names "name" "names"
      simp [bound, callee, binaryEnvironment, BinaryHelper.second, applySubst, Subst.lookup]
    · cases contained : names.contains name with
      | false =>
          simp only [show Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern =
              !(names.contains name) from rfl, contained, Bool.not_false]
          rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
          simpa only [Bool.false_eq_true, ite_false, Effects.boolean] using
            grounded_returns program bound state (.bool true)
      | true =>
          simp only [show Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern =
              !(names.contains name) from rfl, contained, Bool.not_true]
          rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
          simpa only [ite_true, Effects.boolean] using
            grounded_returns program bound state (.bool false)

theorem fresh_returns (state : State) (name : String) (pattern : Pattern) :
    PureReturns program [] state
      (a "gslt:premise:fresh" [encoded (.string name), patternValue pattern]) state
      (Effects.boolean (Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern)) :=
  fresh_captured_returns [] state name pattern _ _ (by simp)

/-- Optional names use the same physical option constructors as the matcher. -/
def nameOptionTerm : Option String → Term
  | none => .symbol "None"
  | some name => .application "Some" [.string name]

private def resolveValueCases : SpaceSemantics.Cases :=
  [(a "FVar" [v "resolved"], a "Some" [v "resolved"]),
   (v "non-name", .symbol "None")]
private def resolveValueBody : Atom :=
  a "case" [v "value", .expression (resolveValueCases.map fun row => .expression [row.1, row.2])]
private def resolveCases : SpaceSemantics.Cases :=
  [(.symbol "None", a "Some" [v "name"]), (a "Some" [v "value"], resolveValueBody)]

private theorem resolve_shape : (binaryEquation .resolve).body =
    a "case" [a "gslt:automata:binding" [v "name", v "bindings"],
      .expression (resolveCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem some_template (name : String) : PureData.Template program (a "Some" [v name]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact .captured name

private theorem binding_lookup_returns (caller : Subst) (state : State) (name : String)
    (bindings : Bindings)
    (captured : [v "name", v "bindings"].map (applySubst caller) =
      [encoded (.string name), bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:automata:binding" [v "name", v "bindings"]) state
      (encoded (MatchAutomataBindingExecution.patternOptionTerm (bindings.lookup name))) := by
  exact RuleExecutionProgram.automata_captured_returns (by decide +kernel)
    (MatchAutomataBindingExecution.binding_captured_returns caller state name bindings _ captured)

private theorem resolve_value_returns (caller : Subst) (state : State) (pattern : Pattern)
    (captured : Subst.lookup caller "value" = some (patternValue pattern))
    (resolvedFresh : Subst.lookup caller "resolved" = none)
    (nonNameFresh : Subst.lookup caller "non-name" = none) :
    PureReturns program caller state resolveValueBody state
      (encoded (nameOptionTerm (match (generalizing := false) pattern with
        | .fvar name => some name | _ => none))) := by
  by_cases named : ∃ name, pattern = .fvar name
  · obtain ⟨name, rfl⟩ := named
    let selected := ("resolved", encoded (.string name)) :: caller
    apply case_returns program caller selected state state state (v "value")
      (patternValue (.fvar name)) (a "Some" [v "resolved"]) _ _ resolveValueCases
      (read_cases_encoded _) _ _ _
    · simpa only [applySubst, captured, Option.getD_some] using variable_returns program caller state "value"
    · simp [resolveValueCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, selected, resolvedFresh]
    · simpa [nameOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        selected, applySubst, applySubst.applySubstList, Subst.lookup] using
        PureData.template_return program selected state (a "Some" [v "resolved"]) (some_template "resolved")
  · have unnamed : (match (generalizing := false) pattern with
        | .fvar name => some name | _ => none : Option String) = none := by
      cases pattern with
      | fvar name => exact False.elim (named ⟨name, rfl⟩)
      | _ => rfl
    rw [unnamed]
    apply case_returns program caller (("non-name", patternValue pattern) :: caller) state state state (v "value")
      (patternValue pattern) (.symbol "None") _ _ resolveValueCases (read_cases_encoded _) _ _ _
    · simpa only [applySubst, captured, Option.getD_some] using variable_returns program caller state "value"
    · cases pattern with
      | fvar name => exact False.elim (named ⟨name, rfl⟩)
      | _ => simp [resolveValueCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, nonNameFresh]
    · exact symbol_returns program _ state "None"

/-- A binding resolves a freshness name only when its payload is a free name.
An absent binding retains the literal name; other payloads refuse it. -/
theorem resolve_name_captured_returns (caller : Subst) (state : State) (name : String)
    (bindings : Bindings) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (.string name), bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:premise:resolve-name" [one, two]) state
      (encoded (nameOptionTerm (match bindings.lookup name with
        | none => some name
        | some (.fvar resolved) => some resolved
        | some _ => none))) := by
  let callee := binaryEnvironment .resolve name (bindingsValue bindings)
  have lookedUp := binding_lookup_returns callee state name bindings
    (by simp [callee, binaryEnvironment, BinaryHelper.second, applySubst, Subst.lookup])
  apply binary_call .resolve caller state name (bindingsValue bindings) one two _ captured
  rw [resolve_shape]
  cases found : bindings.lookup name with
  | none =>
      apply case_returns program callee callee state state state
        (a "gslt:automata:binding" [v "name", v "bindings"]) (.symbol "None")
        (a "Some" [v "name"]) _ _ resolveCases (read_cases_encoded _) _ _ _
      · simpa only [found, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using lookedUp
      · simp [resolveCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [found, nameOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, callee,
          binaryEnvironment, BinaryHelper.second, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program callee state (a "Some" [v "name"]) (some_template "name")
  | some value =>
      let selected := ("value", patternValue value) :: callee
      apply case_returns program callee selected state state state
        (a "gslt:automata:binding" [v "name", v "bindings"])
        (a "Some" [patternValue value]) resolveValueBody _ _ resolveCases (read_cases_encoded _) _ _ _
      · simpa only [found, MatchAutomataBindingExecution.patternOptionTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookedUp
      · simp [resolveCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, callee,
          binaryEnvironment, BinaryHelper.second]
      · have returned := resolve_value_returns selected state value
          (by simp [selected, Subst.lookup])
          (by simp [selected, callee, binaryEnvironment, BinaryHelper.second, Subst.lookup])
          (by simp [selected, callee, binaryEnvironment, BinaryHelper.second, Subst.lookup])
        cases value <;> simpa only [found] using returned

theorem resolve_name_returns (state : State) (name : String) (bindings : Bindings) :
    PureReturns program [] state
      (a "gslt:premise:resolve-name" [encoded (.string name), bindingsValue bindings]) state
      (encoded (nameOptionTerm (match bindings.lookup name with
        | none => some name
        | some (.fvar resolved) => some resolved
        | some _ => none))) :=
  resolve_name_captured_returns [] state name bindings _ _ (by simp)

private abbrev resultsValue (results : List Bindings) : Atom :=
  encoded (RelationPremiseExecution.bindingResultsTerm results)
private def freshnessEquation : SpaceSemantics.Equation :=
  (equations "gslt:premise:freshness")[0]'(by decide +kernel)
private def freshnessEnvironment (name : String) (plan : PatternPlan) (bindings : Bindings) : Subst :=
  [("bindings", bindingsValue bindings), ("term", patternValue plan.erase), ("name", encoded (.string name))]
private def freshnessResolved : Atom :=
  a "let" [v "subject", a "gslt:rule:instantiate" [v "term", v "bindings"],
    a "if" [a "gslt:premise:fresh" [v "atom", v "subject"],
      a "LCons" [v "bindings", .symbol "LNil"], .symbol "LNil"]]
private def freshnessCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "LNil"), (a "Some" [v "atom"], freshnessResolved)]
private def freshnessBody : Atom :=
  a "case" [a "gslt:premise:resolve-name" [v "name", v "bindings"],
    .expression (freshnessCases.map fun row => .expression [row.1, row.2])]

private theorem freshness_shape : freshnessEquation.body = freshnessBody := by decide +kernel

private theorem freshness_clause (name : String) (plan : PatternPlan) (bindings : Bindings) :
    clauses program "gslt:premise:freshness" [encoded (.string name), patternValue plan.erase,
      bindingsValue bindings] = [.evaluate (freshnessEnvironment name plan bindings) freshnessEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:premise:freshness").filterMap _ = _
  rw [show equations "gslt:premise:freshness" = [freshnessEquation] from rfl]
  have formals : freshnessEquation.arguments = [v "name", v "term", v "bindings"] := by decide +kernel
  simp [formals, freshnessEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem singleton_template :
    PureData.Template program (a "LCons" [v "bindings", .symbol "LNil"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .captured "bindings"
  · exact .symbol "LNil"

private theorem freshness_after_resolution (state : State) (name : String) (plan : PatternPlan)
    (bindings : Bindings) (resolved : Option String)
    (returned : PureReturns program (freshnessEnvironment name plan bindings) state
      (a "gslt:premise:resolve-name" [v "name", v "bindings"]) state (encoded (nameOptionTerm resolved))) :
    PureReturns program (freshnessEnvironment name plan bindings) state freshnessBody state
      (resultsValue (match (generalizing := false) resolved with
        | none => []
        | some atom => if Mettapedia.OSLF.MeTTaIL.Substitution.isFresh atom (plan.instantiate bindings)
            then [bindings] else [])) := by
  let caller := freshnessEnvironment name plan bindings
  cases resolved with
  | none =>
      apply case_returns program caller caller state state state
        (a "gslt:premise:resolve-name" [v "name", v "bindings"]) (.symbol "None")
        (.symbol "LNil") _ _ freshnessCases (read_cases_encoded _) _ _ _
      · simpa only [nameOptionTerm, CettaWireAtom.encode] using returned
      · simp [freshnessCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | some atom =>
      let selected := ("atom", encoded (.string atom)) :: caller
      let bound := ("subject", patternValue (plan.instantiate bindings)) :: selected
      apply case_returns program caller selected state state state
        (a "gslt:premise:resolve-name" [v "name", v "bindings"])
        (a "Some" [encoded (.string atom)]) freshnessResolved _ _ freshnessCases (read_cases_encoded _) _ _ _
      · simpa only [nameOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using returned
      · simp [freshnessCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, selected, caller,
          freshnessEnvironment, Subst.lookup]
      · apply let_returns program selected bound state state state (v "subject") _ _
          (patternValue (plan.instantiate bindings)) _
        · exact RuleInstantiationExecution.instantiate_captured_returns selected state bindings plan
            (v "term") (v "bindings")
            (by simp [selected, caller, freshnessEnvironment, applySubst, Subst.lookup])
        · simp [SpaceSemantics.matchValue, matchAtom, selected, caller, freshnessEnvironment,
            Subst.lookup, bound]
        · apply if_returns program bound state state state _
            (Effects.boolean (Mettapedia.OSLF.MeTTaIL.Substitution.isFresh atom (plan.instantiate bindings)))
            (a "LCons" [v "bindings", .symbol "LNil"]) (.symbol "LNil") _
          · apply fresh_captured_returns bound state atom (plan.instantiate bindings) (v "atom") (v "subject")
            simp [bound, selected, caller, freshnessEnvironment, applySubst, Subst.lookup]
          · cases fresh : Mettapedia.OSLF.MeTTaIL.Substitution.isFresh atom (plan.instantiate bindings) with
            | false =>
                simp only [fresh]
                rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
                simpa only [Bool.false_eq_true, ite_false, resultsValue,
                  RelationPremiseExecution.bindingResultsTerm, encodeList, CettaWireAtom.encode] using
                  symbol_returns program bound state "LNil"
            | true =>
                simp only [fresh]
                rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
                simpa [resultsValue, RelationPremiseExecution.bindingResultsTerm, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, bound, selected, caller,
                  freshnessEnvironment, applySubst, applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return program bound state
                    (a "LCons" [v "bindings", .symbol "LNil"]) singleton_template

/-- The shared source realizes the canonical syntactic freshness premise,
including name resolution and substitution of captured full-pattern payloads.
The schema is the existing first-order plan fragment. -/
theorem freshness_captured_returns (caller : Subst) (state : State)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (name : String) (plan : PatternPlan) (bindings : Bindings) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [CettaWireAtom.encode (.string name), CettaWireAtom.encode (InferenceCettaWire.encodePattern plan.erase),
        CettaWireAtom.encode (MatchAutomataBindingExecution.bindingsTerm bindings)]) :
    PureReturns program caller state (.expression [.symbol "gslt:premise:freshness", one, two, three]) state
      (CettaWireAtom.encode (RelationPremiseExecution.bindingResultsTerm
        (Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relations language bindings
        (.freshness {varName := name, term := plan.erase})))) := by
  let callee := freshnessEnvironment name plan bindings
  apply PureData.raw_authored_call_return program caller callee state state
    "gslt:premise:freshness" [one, two, three] freshnessEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ _
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact freshness_clause name plan bindings
  · rw [freshness_shape]
    have resolved := resolve_name_captured_returns callee state name bindings (v "name") (v "bindings")
      (by simp [callee, freshnessEnvironment, applySubst, Subst.lookup])
    have composed := freshness_after_resolution state name plan bindings _ resolved
    have interpretation : Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relations language bindings
        (.freshness {varName := name, term := plan.erase}) =
        (match bindings.lookup name with
          | none => if Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name
              (applyBindings bindings plan.erase) then [bindings] else []
          | some (.fvar atom) => if Mettapedia.OSLF.MeTTaIL.Substitution.isFresh atom
              (applyBindings bindings plan.erase) then [bindings] else []
          | some _ => []) := by
      change
        (match (match bindings.lookup name with
          | some (.fvar atom) => some atom
          | some _ => none
          | none => some name) with
        | some atom => if Mettapedia.OSLF.MeTTaIL.Substitution.isFresh atom
            (applyBindings bindings plan.erase) then [bindings] else []
        | none => []) = _
      cases found : bindings.lookup name with
      | none => rfl
      | some value => cases value <;> rfl
    rw [interpretation]
    cases found : bindings.lookup name with
    | none => simpa only [found, instantiate_eq_applyBindings] using composed
    | some value => cases value <;> simpa only [found, instantiate_eq_applyBindings] using composed

theorem freshness_returns (state : State)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (name : String) (plan : PatternPlan) (bindings : Bindings) :
    PureReturns program [] state
      (a "gslt:premise:freshness" [encoded (.string name), patternValue plan.erase, bindingsValue bindings]) state
      (resultsValue (Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relations language bindings
        (.freshness {varName := name, term := plan.erase}))) :=
  freshness_captured_returns [] state relations language name plan bindings _ _ _ (by simp)

theorem freshness_completed_iff (state : State)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (name : String) (plan : PatternPlan) (bindings : Bindings)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state := state, control := .evaluate [] (a "gslt:premise:freshness"
          [encoded (.string name), patternValue plan.erase, bindingsValue bindings]) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [resultsValue
        (Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relations language bindings
          (.freshness {varName := name, term := plan.erase}))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (freshness_returns state relations language name plan bindings) after answers input output

theorem freshness_derivation_iff (state : State)
    (relations : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv) (language : LanguageDef)
    (name : String) (plan : PatternPlan) (bindings : Bindings)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state := state, control := .evaluate [] (a "gslt:premise:freshness"
          [encoded (.string name), patternValue plan.erase, bindingsValue bindings]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue
        (Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relations language bindings
          (.freshness {varName := name, term := plan.erase}))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (freshness_returns state relations language name plan bindings) after answers input output

/-! ## Lexical parameters for the existing typed premise semantics -/
namespace QuantifiedLocal

open Mettapedia.OSLF.MeTTaIL
open RuleBinding ScopedRuleMatching

private inductive Helper where | remove | bind | restore | localValue | collection
private def Helper.head : Helper → String
  | .remove => "gslt:premise:scope-remove"
  | .bind => "gslt:premise:scope-bind"
  | .restore => "gslt:premise:scope-restore"
  | .localValue => "gslt:premise:scope-local-value"
  | .collection => "gslt:premise:scope-collection"
private def Helper.names : Helper → List String
  | .remove => ["parameter", "assignment"]
  | .bind => ["parameter", "value", "assignment"]
  | .restore => ["parameter", "initial", "final"]
  | .localValue => ["ambient", "pattern"]
  | .collection => ["ambient", "assignment", "name"]
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse
private abbrev assignmentValue (assignment : Assignment) : Atom :=
  encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)
private abbrev contextualValue (value : ContextualValue) : Atom :=
  encoded (InferenceCettaWire.AuthoredRule.contextualValueTerm value)
attribute [local simp] assignmentValue contextualValue

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values =
      [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases small with rfl | rfl | rfl <;> first | omega | decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (environment helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem named_let_returns (caller : Subst) (state : State) (name : String)
    (expression value body answer : Atom) (fresh : Subst.lookup caller name = none)
    (computed : PureReturns program caller state expression state value)
    (continued : PureReturns program ((name, value) :: caller) state body state answer) :
    PureReturns program caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns program caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed _ continued
  simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]

private theorem bool_if_returns (caller : Subst) (state : State) (condition : Atom)
    (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (returned : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have same : (Effects.boolean value == Effects.boolean true) = value := by cases value <;> decide +kernel
  simpa only [same] using returned

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body : Atom) {answer : Atom}
    (computed : PureReturns program caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns program caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private def removeCons : Atom :=
  a "let" [v "tail", a Helper.remove.head [v "parameter", v "rest"],
    a "if" [a "==" [v "name", v "parameter"], v "tail",
      a "let" [v "entry", a "Binding" [v "name", v "value"], a "LCons" [v "entry", v "tail"]]]]
private def removeCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "Binding" [v "name", v "value"], v "rest"], removeCons)]
private theorem remove_shape : (equation .remove).body =
    a "case" [v "assignment", .expression (removeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- Every occurrence of the local name is removed; opaque captures and the
order of all other entries are retained by the actual source equation. -/
theorem remove_parameter_returns (state : State) (parameter : String) (assignment : Assignment) :
    PureReturns program [] state
      (a "gslt:premise:scope-remove" [encoded (.string parameter), assignmentValue assignment]) state
      (assignmentValue (GeneralPremise.removeParameter parameter assignment)) := by
  induction assignment with
  | nil =>
      let caller := environment .remove [encoded (.string parameter), assignmentValue []]
      apply helper_call .remove [] state _ [encoded (.string parameter), assignmentValue []] _ rfl (by simp)
      rw [remove_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") removeCases (.symbol "LNil")
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup,
          RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, encodeList, CettaWireAtom.encode] using
          variable_returns program caller state "assignment"
      · simp [removeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      let caller := environment .remove [encoded (.string parameter), assignmentValue ((name, value) :: rest)]
      let selected := ("rest", assignmentValue rest) :: ("value", contextualValue value) ::
        ("name", encoded (.string name)) :: caller
      let tail := assignmentValue (GeneralPremise.removeParameter parameter rest)
      let extended := ("tail", tail) :: selected
      apply helper_call .remove [] state _ [encoded (.string parameter), assignmentValue ((name, value) :: rest)] _ rfl (by simp)
      rw [remove_shape]
      apply branch_returns caller selected state _ (assignmentValue ((name, value) :: rest))
        removeCases removeCons
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns program caller state "assignment"
      · simp [removeCases, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, caller, environment, Helper.names]
      · unfold removeCons
        apply named_let_returns selected state "tail" _ tail _ _
        · simp [selected, caller, environment, Helper.names, Subst.lookup]
        · apply helper_capture .remove selected state _ [encoded (.string parameter), assignmentValue rest] _ rfl _ ih
          simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup]
        · apply bool_if_returns extended state _ (decide (name = parameter))
          · simpa only [Term.string.injEq] using
              CettaWireAtom.equality_captured_returns program extended state (.string name) (.string parameter)
                "name" "parameter" (by simp [extended, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
                (by simp [extended, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
          · by_cases same : name = parameter
            · subst name
              simpa [GeneralPremise.removeParameter, tail, extended, selected, caller, environment,
                Helper.names, applySubst, Subst.lookup] using variable_returns program extended state "tail"
            · simp only [same, decide_false, Bool.false_eq_true, ite_false]
              apply named_let_returns extended state "entry" _ (a "Binding" [encoded (.string name), contextualValue value]) _ _
              · simp [extended, selected, caller, environment, Helper.names, Subst.lookup]
              · simpa [extended, selected, caller, environment, Helper.names, applySubst, Subst.lookup] using
                  constructor_variables_return program extended state "Binding" ["name", "value"]
                    (by decide +kernel) (by decide)
              · simpa [GeneralPremise.removeParameter, same, tail, extended, selected, caller, environment,
                  Helper.names, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
                  MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, Subst.lookup] using
                  constructor_variables_return program
                    (("entry", a "Binding" [encoded (.string name), contextualValue value]) :: extended)
                    state "LCons" ["entry", "tail"] (by decide +kernel) (by decide)

theorem remove_parameter_captured_returns (caller : Subst) (state : State) (parameter : String)
    (assignment : Assignment) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string parameter), assignmentValue assignment]) :
    PureReturns program caller state (a "gslt:premise:scope-remove" [one, two]) state
      (assignmentValue (GeneralPremise.removeParameter parameter assignment)) :=
  helper_capture .remove caller state [one, two] [encoded (.string parameter), assignmentValue assignment] _ rfl captured (remove_parameter_returns state parameter assignment)

private def bindBody : Atom :=
  a "let*" [.expression
    [.expression [v "rest", a Helper.remove.head [v "parameter", v "assignment"]],
     .expression [v "entry", a "Binding" [v "parameter", v "value"]]],
    a "LCons" [v "entry", v "rest"]]
private theorem bind_shape : (equation .bind).body = bindBody := by decide +kernel

/-- A local binding shadows every older binding of the same name. -/
theorem bind_parameter_returns (state : State) (parameter : String) (value : ContextualValue)
    (assignment : Assignment) :
    PureReturns program [] state
      (a "gslt:premise:scope-bind" [encoded (.string parameter), contextualValue value, assignmentValue assignment]) state
      (assignmentValue (GeneralPremise.bindParameter parameter value assignment)) := by
  let caller := environment .bind [encoded (.string parameter), contextualValue value, assignmentValue assignment]
  let rest := assignmentValue (GeneralPremise.removeParameter parameter assignment)
  let bound := ("rest", rest) :: caller
  let entry := a "Binding" [encoded (.string parameter), contextualValue value]
  apply helper_call .bind [] state _ [encoded (.string parameter), contextualValue value, assignmentValue assignment] _ rfl (by simp)
  rw [bind_shape]
  apply PureData.let_bindings_return
    (pairs := [(v "rest", a Helper.remove.head [v "parameter", v "assignment"]),
      (v "entry", a "Binding" [v "parameter", v "value"])])
    (final := ("entry", entry) :: bound)
  · apply PureData.BindingsReturn.cons (bound := bound)
    · exact remove_parameter_captured_returns caller state parameter assignment _ _
        (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
    · simp [SpaceSemantics.matchValue, matchAtom, caller, environment, Helper.names, bound, rest, Subst.lookup]
    · apply PureData.BindingsReturn.cons (bound := ("entry", entry) :: bound)
      · simpa [bound, caller, environment, Helper.names, applySubst, Subst.lookup] using
          constructor_variables_return program bound state "Binding" ["parameter", "value"]
            (by decide +kernel) (by decide)
      · simp [SpaceSemantics.matchValue, matchAtom, bound, entry, caller, environment, Helper.names, Subst.lookup]
      · exact .nil _ _
  · simpa [GeneralPremise.bindParameter, rest, entry, bound, caller, environment, Helper.names,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, encodeList, CettaWireAtom.encode,
      CettaWireAtom.encodeMany, applySubst, Subst.lookup] using
      constructor_variables_return program (("entry", entry) :: bound) state "LCons" ["entry", "rest"]
        (by decide +kernel) (by decide)

theorem bind_parameter_captured_returns (caller : Subst) (state : State) (parameter : String)
    (value : ContextualValue) (assignment : Assignment) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (.string parameter), contextualValue value, assignmentValue assignment]) :
    PureReturns program caller state (a "gslt:premise:scope-bind" [one, two, three]) state
      (assignmentValue (GeneralPremise.bindParameter parameter value assignment)) :=
  helper_capture .bind caller state [one, two, three] [encoded (.string parameter), contextualValue value, assignmentValue assignment] _ rfl captured (bind_parameter_returns state parameter value assignment)

private theorem binding_captured_returns (caller : Subst) (state : State) (name : String)
    (assignment : Assignment) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [encoded (.string name), assignmentValue assignment]) :
    PureReturns program caller state (a "gslt:automata:binding" [v one, v two]) state
      (encoded (MatchAutomataBindingExecution.payloadOptionTerm
        ((ScopedRuleMatching.lookup assignment name).map InferenceCettaWire.AuthoredRule.contextualValueTerm))) := by
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  simpa only [RuleInstantiationExecution.ScopedCapture.scoped_lookup_wire] using
    MatchAutomataBindingExecution.payload_binding_captured_returns caller state name
      (assignment.map fun entry => (entry.1, InferenceCettaWire.AuthoredRule.contextualValueTerm entry.2))
      [v one, v two] (by simpa only [assignmentValue, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm] using captured)

private def restoreCases : SpaceSemantics.Cases :=
  [(.symbol "None", a Helper.remove.head [v "parameter", v "final"]),
   (a "Some" [v "value"], a Helper.bind.head [v "parameter", v "value", v "final"])]
private theorem restore_shape : (equation .restore).body =
    a "case" [a "gslt:automata:binding" [v "parameter", v "initial"],
      .expression (restoreCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

/-- The original parameter is restored exactly; successful body outputs at
all other names survive. The actual source uses first-occurrence lookup. -/
theorem restore_parameter_returns (state : State) (parameter : String) (initial final : Assignment) :
    PureReturns program [] state
      (a "gslt:premise:scope-restore" [encoded (.string parameter), assignmentValue initial, assignmentValue final]) state
      (assignmentValue (GeneralPremise.restoreParameter parameter initial final)) := by
  let caller := environment .restore [encoded (.string parameter), assignmentValue initial, assignmentValue final]
  apply helper_call .restore [] state _ [encoded (.string parameter), assignmentValue initial, assignmentValue final] _ rfl (by simp)
  rw [restore_shape]
  cases found : ScopedRuleMatching.lookup initial parameter with
  | none =>
      apply branch_returns caller caller state _ (.symbol "None") restoreCases
        (a Helper.remove.head [v "parameter", v "final"])
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using
          binding_captured_returns caller state parameter initial _ _
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [restoreCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [GeneralPremise.restoreParameter, found, GeneralPremise.bindParameter, Helper.head] using
          remove_parameter_captured_returns caller state parameter final _ _
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
  | some value =>
      let selected := ("value", contextualValue value) :: caller
      apply branch_returns caller selected state _ (a "Some" [contextualValue value]) restoreCases
        (a Helper.bind.head [v "parameter", v "value", v "final"])
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          binding_captured_returns caller state parameter initial _ _
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [restoreCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, caller, environment, Helper.names]
      · simpa [GeneralPremise.restoreParameter, found, GeneralPremise.bindParameter, Helper.head] using
          bind_parameter_captured_returns selected state parameter value final _ _ _
            (by simp [selected, caller, environment, Helper.names, applySubst, Subst.lookup])

theorem restore_parameter_captured_returns (caller : Subst) (state : State) (parameter : String)
    (initial final : Assignment) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (.string parameter), assignmentValue initial, assignmentValue final]) :
    PureReturns program caller state (a "gslt:premise:scope-restore" [one, two, three]) state
      (assignmentValue (GeneralPremise.restoreParameter parameter initial final)) :=
  helper_capture .restore caller state [one, two, three] [encoded (.string parameter), assignmentValue initial, assignmentValue final] _ rfl captured (restore_parameter_returns state parameter initial final)

private theorem local_value_shape : (equation .localValue).body =
    a "ContextualValue" [.symbol "LNil", v "ambient", v "pattern"] := by decide +kernel

/-- A collection element retains the surrounding ambient context and has no
higher-order dependency parameters. Its body remains opaque data. -/
theorem local_value_returns (state : State) (bound : List TypeExpr) (pattern : Pattern) :
    PureReturns program [] state
      (a "gslt:premise:scope-local-value" [encoded (.natural bound.length), patternValue pattern]) state
      (contextualValue (GeneralPremise.localValue bound pattern)) := by
  let caller := environment .localValue [encoded (.natural bound.length), patternValue pattern]
  apply helper_call .localValue [] state _ [encoded (.natural bound.length), patternValue pattern] _ rfl (by simp)
  rw [local_value_shape]
  have template : PureData.Template program (a "ContextualValue" [.symbol "LNil", v "ambient", v "pattern"]) := by
    apply PureData.Template.constructor "ContextualValue" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .symbol _
    · exact .captured _
    · exact .captured _
  simpa [GeneralPremise.localValue, InferenceCettaWire.AuthoredRule.contextualValueTerm,
    InferenceCettaWire.encodeList, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    caller, environment, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup] using
    PureData.template_return program caller state _ template

/-- Optional finite collections use the shared Pattern and list wire. `None`
means refusal; a concrete empty collection is `Some (FiniteCollection ... LNil)`. -/
def finiteCollectionOptionTerm : Option (CollType × List Pattern) → Term :=
  encodeOption fun value => .application "FiniteCollection"
    [InferenceCettaWire.encodeCollectionType value.1,
      InferenceCettaWire.encodePatterns value.2]

private def concreteCases : SpaceSemantics.Cases :=
  [(a "PCollection" [v "kind", v "elements", .symbol "RNone"],
    a "Some" [a "FiniteCollection" [v "kind", v "elements"]]),
   (v "non-concrete", .symbol "None")]
private def collectionPatternBody : Atom :=
  a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])]
private def projectedCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "pattern"], collectionPatternBody)]
private def collectionValueBody : Atom :=
  a "case" [a "gslt:rule:scope-instantiate-value" [v "value", v "ambient", encoded (.natural 0), .symbol "LNil"],
    .expression (projectedCases.map fun row => .expression [row.1, row.2])]
private def collectionCases : SpaceSemantics.Cases :=
  [(.symbol "None", .symbol "None"), (a "Some" [v "value"], collectionValueBody)]
private theorem collection_shape : (equation .collection).body =
    a "case" [a "gslt:automata:binding" [v "name", v "assignment"],
      .expression (collectionCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem different_head_rejected (caller : Subst) (head : String) (arguments : List Atom)
    (different : head ≠ "PCollection") :
    SpaceSemantics.matchValue caller (a "PCollection" [v "kind", v "elements", .symbol "RNone"])
      (a head arguments) = none := by
  rw [SpaceSemantics.matchValue_expression_of_not_cons caller _ _ (by intro first rest; simp)]
  simp only [SpaceSemantics.matchValue.matchValues]
  have rejected : SpaceSemantics.matchValue caller (.symbol "PCollection") (.symbol head) = none := by
    simp [SpaceSemantics.matchValue, matchAtom, Ne.symm different]
  rw [rejected]
  rfl

private theorem concrete_collection_returns (caller : Subst) (state : State) (pattern : Pattern)
    (captured : applySubst caller (v "pattern") = patternValue pattern)
    (fresh : ∀ name ∈ ["kind", "elements", "non-concrete"], Subst.lookup caller name = none) :
    PureReturns program caller state collectionPatternBody state
      (encoded (finiteCollectionOptionTerm (GeneralPremise.concreteCollection? pattern))) := by
  unfold collectionPatternBody
  simp only [Subst.lookup] at fresh
  have computed : PureReturns program caller state (v "pattern") state (patternValue pattern) := by
    simpa only [captured] using variable_returns program caller state "pattern"
  cases pattern
  case collection kind elements rest =>
      cases rest with
      | none =>
          let selected := ("elements", patternsValue elements) ::
            ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
          apply branch_returns caller selected state _ (patternValue (.collection kind elements none))
            concreteCases (a "Some" [a "FiniteCollection" [v "kind", v "elements"]]) computed
          · simp [concreteCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, InferenceCettaWire.encodeRest, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              selected, fresh "kind" (by simp), fresh "elements" (by simp), Subst.lookup]
          · have template : PureData.Template program (a "Some" [a "FiniteCollection" [v "kind", v "elements"]]) := by
              apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
              intro argument member
              simp only [List.mem_singleton] at member
              subst argument
              apply PureData.Template.constructor "FiniteCollection" _ (by decide +kernel) (by decide)
              intro argument member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> exact .captured _
            simpa [GeneralPremise.concreteCollection?, finiteCollectionOptionTerm, selected, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup] using PureData.template_return program selected state _ template
      | some rest =>
          apply branch_returns caller (("non-concrete", patternValue (.collection kind elements (some rest))) :: caller)
            state _ (patternValue (.collection kind elements (some rest))) concreteCases (.symbol "None") computed
          · simp [concreteCases, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeRest,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              fresh "non-concrete" (by simp), Subst.lookup]
          · exact symbol_returns program _ state "None"
  case bvar index =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.bvar index)) = none := by
      simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "Var" [encoded (.natural index)] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.bvar index)) :: caller) state _ (patternValue (.bvar index))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

  case fvar name =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.fvar name)) = none := by
      simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "FVar" [encoded (.string name)] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.fvar name)) :: caller) state _ (patternValue (.fvar name))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

  case apply head children =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.apply head children)) = none := by
      simpa only [patternValue, patternsValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "PApp" [encoded (.string head), patternsValue children] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.apply head children)) :: caller) state _ (patternValue (.apply head children))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

  case lambda binder body =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.lambda binder body)) = none := by
      simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "PLam"
          [encoded (InferenceCettaWire.encodeBinder binder), patternValue body] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.lambda binder body)) :: caller) state _ (patternValue (.lambda binder body))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

  case multiLambda arity binders body =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.multiLambda arity binders body)) = none := by
      simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "PMultiLam" [encoded (.natural arity),
          encoded (InferenceCettaWire.encodeList Term.string binders), patternValue body] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.multiLambda arity binders body)) :: caller) state _ (patternValue (.multiLambda arity binders body))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

  case subst body replacement =>
    have rejected : SpaceSemantics.matchValue caller
        (a "PCollection" [v "kind", v "elements", .symbol "RNone"]) (patternValue (.subst body replacement)) = none := by
      simpa only [patternValue, encoded, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        different_head_rejected caller "PSubst" [patternValue body, patternValue replacement] (by decide)
    change PureReturns program caller state
      (a "case" [v "pattern", .expression (concreteCases.map fun row => .expression [row.1, row.2])])
      state (.symbol "None")
    apply branch_returns caller (("non-concrete", patternValue (.subst body replacement)) :: caller) state _ (patternValue (.subst body replacement))
      concreteCases (.symbol "None") computed
    · simp only [concreteCases, SpaceSemantics.selectCase, rejected]
      simp [SpaceSemantics.matchValue, matchAtom, fresh "non-concrete" (by simp), Subst.lookup]
    · exact symbol_returns program _ state "None"

/-- Collection reading executes the canonical contextual projection first.
Missing, wrong-context, wrong-arity, ill-scoped and open-rest values are
refused without turning them into successful empty quantification. -/
theorem finite_collection_returns (state : State) (ambient : Nat) (assignment : Assignment) (name : String) :
    PureReturns program [] state
      (a "gslt:premise:scope-collection" [encoded (.natural ambient), assignmentValue assignment, encoded (.string name)]) state
      (encoded (finiteCollectionOptionTerm (GeneralPremise.finiteCollection? ambient assignment name))) := by
  let caller := environment .collection [encoded (.natural ambient), assignmentValue assignment, encoded (.string name)]
  apply helper_call .collection [] state _
    [encoded (.natural ambient), assignmentValue assignment, encoded (.string name)] _ rfl (by simp)
  rw [collection_shape]
  cases found : ScopedRuleMatching.lookup assignment name with
  | none =>
      apply branch_returns caller caller state _ (.symbol "None") collectionCases (.symbol "None")
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode] using
          binding_captured_returns caller state name assignment "name" "assignment"
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [collectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [GeneralPremise.finiteCollection?, found, finiteCollectionOptionTerm, CettaWireAtom.encode] using
          symbol_returns program caller state "None"
  | some value =>
      let valueBound := ("value", contextualValue value) :: caller
      apply branch_returns caller valueBound state _ (a "Some" [contextualValue value]) collectionCases collectionValueBody
      · simpa [found, MatchAutomataBindingExecution.payloadOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
          binding_captured_returns caller state name assignment "name" "assignment"
            (by simp [caller, environment, Helper.names, applySubst, Subst.lookup])
      · simp [collectionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          valueBound, caller, environment, Helper.names]
      · unfold collectionValueBody
        have instantiated := RuleInstantiationExecution.ScopedCapture.instantiate_value_captured_returns
          valueBound state value ambient 0 [] (v "value") (v "ambient") (encoded (.natural 0)) (.symbol "LNil")
          (by simp [valueBound, caller, environment, Helper.names, applySubst, Subst.lookup,
            InferenceCettaWire.encodePatterns, CettaWireAtom.encode])
        cases projected : RuleBinding.instantiateValue? value ambient 0 [] with
        | none =>
            apply branch_returns valueBound valueBound state _ (.symbol "None") projectedCases (.symbol "None")
            · simpa [projected, MatchAutomataBindingExecution.patternOptionTerm, CettaWireAtom.encode] using instantiated
            · simp [projectedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · simpa [GeneralPremise.finiteCollection?, found, projected, finiteCollectionOptionTerm, CettaWireAtom.encode] using
                symbol_returns program valueBound state "None"
        | some pattern =>
            let patternBound := ("pattern", patternValue pattern) :: valueBound
            apply branch_returns valueBound patternBound state _ (a "Some" [patternValue pattern]) projectedCases collectionPatternBody
            · simpa [projected, MatchAutomataBindingExecution.patternOptionTerm,
                CettaWireAtom.encode, CettaWireAtom.encodeMany] using instantiated
            · simp [projectedCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                patternBound, valueBound, caller, environment, Helper.names]
            · simpa [GeneralPremise.finiteCollection?, found, projected] using
                concrete_collection_returns patternBound state pattern
                  (by simp [patternBound, valueBound, caller, environment, Helper.names, applySubst, Subst.lookup])
                  (by intro name member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                      rcases member with rfl | rfl | rfl <;>
                        simp [patternBound, valueBound, caller, environment, Helper.names, Subst.lookup])

theorem finite_collection_captured_returns (caller : Subst) (state : State)
    (ambient : Nat) (assignment : Assignment) (name : String) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (.natural ambient), assignmentValue assignment, encoded (.string name)]) :
    PureReturns program caller state (a "gslt:premise:scope-collection" [one, two, three]) state
      (encoded (finiteCollectionOptionTerm (GeneralPremise.finiteCollection? ambient assignment name))) :=
  helper_capture .collection caller state [one, two, three]
    [encoded (.natural ambient), assignmentValue assignment, encoded (.string name)] _ rfl captured
    (finite_collection_returns state ambient assignment name)

#print axioms finite_collection_returns
#print axioms finite_collection_captured_returns

#print axioms remove_parameter_returns
#print axioms bind_parameter_returns
#print axioms restore_parameter_returns
#print axioms local_value_returns

/-- A suspended caller may supply the ambient size and element through raw
arguments without evaluating the element's body. -/
theorem local_value_captured_returns (caller : Subst) (state : State)
    (bound : List TypeExpr) (pattern : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (.natural bound.length), patternValue pattern]) :
    PureReturns program caller state (a "gslt:premise:scope-local-value" [one, two]) state
      (contextualValue (GeneralPremise.localValue bound pattern)) :=
  helper_capture .localValue caller state [one, two]
    [encoded (.natural bound.length), patternValue pattern] _ rfl captured
    (local_value_returns state bound pattern)

#print axioms local_value_captured_returns

end QuantifiedLocal

/-! ## Authored constructor-parameter guards -/
namespace TypedParameters

open Mettapedia.GSLT.LanguageDef.WellSorted
open InferenceCettaWire.AuthoredRule

attribute [local simp] InferenceCettaWire.encodeList

private def typeEquation : SpaceSemantics.Equation :=
  (equations "gslt:premise:parameter-type")[0]'(by decide +kernel)
private def typeEnvironment (parameter : TermParam) : Subst :=
  [("parameter", encoded (parameterTerm parameter))]
private abbrev typeValue (type : TypeExpr) : Atom := encoded (typeTerm type)
private def typeResult (result : Option TypeExpr) : Atom :=
  encoded (CettaWire.encodeOption typeTerm result)

private def singleArrowResult : Atom := a "Some" [a "TArrow" [v "domain", v "codomain"]]
private def singleBaseResult : Atom := a "Some" [a "TArrow" [a "TBase" [v "sort"], a "TBase" [v "sort"]]]
private def singleCases : SpaceSemantics.Cases :=
  [(a "TArrow" [v "domain", v "codomain"], singleArrowResult),
   (a "TBase" [v "sort"], singleBaseResult), (v "bad", .symbol "None")]
private def singleBody : Atom :=
  a "case" [v "type", .expression (singleCases.map fun row => .expression [row.1, row.2])]
private def multiArrowResult : Atom :=
  a "Some" [a "TArrow" [a "TMultiBinder" [v "domain"], v "codomain"]]
private def multiBaseResult : Atom :=
  a "Some" [a "TArrow" [a "TMultiBinder" [a "TBase" [v "sort"]], a "TBase" [v "sort"]]]
private def multiCases : SpaceSemantics.Cases :=
  [(a "TArrow" [a "TMultiBinder" [v "domain"], v "codomain"], multiArrowResult),
   (a "TBase" [v "sort"], multiBaseResult), (v "bad", .symbol "None")]
private def multiBody : Atom :=
  a "case" [v "type", .expression (multiCases.map fun row => .expression [row.1, row.2])]
private def typeCases : SpaceSemantics.Cases :=
  [(a "TermSimple" [v "name", v "type"], a "Some" [v "type"]),
   (a "TermAbstraction" [v "binder", v "name", v "type"], singleBody),
   (a "TermMultiAbstraction" [v "binders", v "name", v "type"], multiBody),
   (v "bad", .symbol "None")]
private theorem type_shape : typeEquation.body =
    a "case" [v "parameter", .expression (typeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem type_data_template (head : String) (arguments : List Atom)
    (supported : head ∈ ["Some", "TArrow", "TBase", "TMultiBinder"])
    (children : ∀ argument ∈ arguments, PureData.Template program argument) :
    PureData.Template program (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at supported
    rcases supported with rfl | rfl | rfl | rfl <;> decide

private theorem some_template (body : Atom) (checked : PureData.Template program body) :
    PureData.Template program (a "Some" [body]) := by
  apply type_data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact checked

private theorem base_template : PureData.Template program (a "TBase" [v "sort"]) := by
  apply type_data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .captured _

private theorem multi_template (body : Atom) (checked : PureData.Template program body) :
    PureData.Template program (a "TMultiBinder" [body]) := by
  apply type_data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact checked

private theorem arrow_template (domain codomain : Atom)
    (left : PureData.Template program domain) (right : PureData.Template program codomain) :
    PureData.Template program (a "TArrow" [domain, codomain]) := by
  apply type_data_template _ _ (by simp)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

private theorem single_annotation_returns (caller : Subst) (state : State) (binder : Option String)
    (name : String) (type : TypeExpr)
    (stored : Subst.lookup caller "type" = some (typeValue type))
    (domainFresh : Subst.lookup caller "domain" = none)
    (codomainFresh : Subst.lookup caller "codomain" = none)
    (sortFresh : Subst.lookup caller "sort" = none)
    (badFresh : Subst.lookup caller "bad" = none) :
    PureReturns program caller state singleBody state
      (typeResult (parameterType? (.abstractionNamed binder name type))) := by
  have read : PureReturns program caller state (v "type") state (typeValue type) := by
    simpa [v, applySubst, stored] using variable_returns program caller state "type"
  simp only [Subst.lookup] at domainFresh codomainFresh sortFresh badFresh
  cases type with
  | arrow domain codomain =>
      let selected := ("codomain", typeValue codomain) :: ("domain", typeValue domain) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.arrow domain codomain)) singleArrowResult _ _ singleCases
        (read_cases_encoded _) read _ _
      · simp [singleCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, domainFresh, codomainFresh, selected, Subst.lookup]
      · simpa [singleArrowResult, selected, typeResult, parameterType?, CettaWire.encodeOption,
          typeValue, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program selected state singleArrowResult
            (some_template _ (arrow_template _ _ (.captured _) (.captured _)))
  | base sort =>
      let selected := ("sort", encoded (.string sort)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.base sort)) singleBaseResult _ _ singleCases (read_cases_encoded _) read _ _
      · simp [singleCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, sortFresh, selected, Subst.lookup]
      · simpa [singleBaseResult, selected, typeResult, parameterType?, CettaWire.encodeOption,
          typeValue, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program selected state singleBaseResult
            (some_template _ (arrow_template _ _ base_template base_template))
  | multiBinder body =>
      let selected := ("bad", typeValue (.multiBinder body)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.multiBinder body)) (.symbol "None") _ _ singleCases (read_cases_encoded _) read _ _
      · simp [singleCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
      · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
          symbol_returns program selected state "None"
  | collection kind element =>
      let selected := ("bad", typeValue (.collection kind element)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.collection kind element)) (.symbol "None") _ _ singleCases (read_cases_encoded _) read _ _
      · simp [singleCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
      · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
          symbol_returns program selected state "None"

private theorem multi_annotation_returns (caller : Subst) (state : State) (binders : List String)
    (name : String) (type : TypeExpr)
    (stored : Subst.lookup caller "type" = some (typeValue type))
    (domainFresh : Subst.lookup caller "domain" = none)
    (codomainFresh : Subst.lookup caller "codomain" = none)
    (sortFresh : Subst.lookup caller "sort" = none)
    (badFresh : Subst.lookup caller "bad" = none) :
    PureReturns program caller state multiBody state
      (typeResult (parameterType? (.multiAbstractionNamed binders name type))) := by
  have read : PureReturns program caller state (v "type") state (typeValue type) := by
    simpa [v, applySubst, stored] using variable_returns program caller state "type"
  simp only [Subst.lookup] at domainFresh codomainFresh sortFresh badFresh
  cases type with
  | base sort =>
      let selected := ("sort", encoded (.string sort)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.base sort)) multiBaseResult _ _ multiCases (read_cases_encoded _) read _ _
      · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, sortFresh, selected, Subst.lookup]
      · simpa [multiBaseResult, selected, typeResult, parameterType?, CettaWire.encodeOption,
          typeValue, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program selected state multiBaseResult
            (some_template _ (arrow_template _ _ (multi_template _ base_template) base_template))
  | arrow domain codomain =>
      cases domain with
      | multiBinder element =>
          let selected := ("codomain", typeValue codomain) :: ("domain", typeValue element) :: caller
          apply case_returns program caller selected state state state (v "type")
            (typeValue (.arrow (.multiBinder element) codomain)) multiArrowResult _ _ multiCases
            (read_cases_encoded _) read _ _
          · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, domainFresh, codomainFresh,
              selected, Subst.lookup]
          · simpa [multiArrowResult, selected, typeResult, parameterType?, CettaWire.encodeOption,
              typeValue, typeTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return program selected state multiArrowResult
                (some_template _ (arrow_template _ _ (multi_template _ (.captured _)) (.captured _)))
      | base sort =>
          let selected := ("bad", typeValue (.arrow (.base sort) codomain)) :: caller
          apply case_returns program caller selected state state state (v "type")
            (typeValue (.arrow (.base sort) codomain)) (.symbol "None") _ _ multiCases (read_cases_encoded _) read _ _
          · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
          · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
      | arrow first second =>
          let selected := ("bad", typeValue (.arrow (.arrow first second) codomain)) :: caller
          apply case_returns program caller selected state state state (v "type")
            (typeValue (.arrow (.arrow first second) codomain)) (.symbol "None") _ _ multiCases (read_cases_encoded _) read _ _
          · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
          · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
      | collection kind element =>
          let selected := ("bad", typeValue (.arrow (.collection kind element) codomain)) :: caller
          apply case_returns program caller selected state state state (v "type")
            (typeValue (.arrow (.collection kind element) codomain)) (.symbol "None") _ _ multiCases (read_cases_encoded _) read _ _
          · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
          · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
  | multiBinder body =>
      let selected := ("bad", typeValue (.multiBinder body)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.multiBinder body)) (.symbol "None") _ _ multiCases (read_cases_encoded _) read _ _
      · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
      · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
          symbol_returns program selected state "None"
  | collection kind element =>
      let selected := ("bad", typeValue (.collection kind element)) :: caller
      apply case_returns program caller selected state state state (v "type")
        (typeValue (.collection kind element)) (.symbol "None") _ _ multiCases (read_cases_encoded _) read _ _
      · simp [multiCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeValue, typeTerm,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, badFresh, selected, Subst.lookup]
      · simpa [typeResult, parameterType?, CettaWire.encodeOption, CettaWireAtom.encode] using
          symbol_returns program selected state "None"

private theorem type_body_returns (state : State) (parameter : TermParam) :
    PureReturns program (typeEnvironment parameter) state typeEquation.body state
      (typeResult (parameterType? parameter)) := by
  rw [type_shape]
  have read : PureReturns program (typeEnvironment parameter) state (v "parameter") state
      (encoded (parameterTerm parameter)) := by
    simpa [v, typeEnvironment, applySubst, Subst.lookup] using
      variable_returns program (typeEnvironment parameter) state "parameter"
  cases parameter with
  | simple name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        typeEnvironment (.simple name type)
      apply case_returns program (typeEnvironment (.simple name type)) selected state state state
        (v "parameter") (encoded (parameterTerm (.simple name type))) (a "Some" [v "type"])
        _ _ typeCases (read_cases_encoded _) read _ _
      · simp [typeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · simpa [selected, typeResult, parameterType?, CettaWire.encodeOption,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program selected state (a "Some" [v "type"])
            (some_template _ (.captured _))
  | abstractionNamed binder name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) ::
        typeEnvironment (.abstractionNamed binder name type)
      apply case_returns program (typeEnvironment (.abstractionNamed binder name type)) selected
        state state state (v "parameter") (encoded (parameterTerm (.abstractionNamed binder name type)))
        singleBody _ _ typeCases (read_cases_encoded _) read _ _
      · simp [typeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · exact single_annotation_returns selected state binder name type
          (by simp [selected, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
  | multiAbstractionNamed binders name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        ("binders", encoded (encodeList Term.string binders)) ::
        typeEnvironment (.multiAbstractionNamed binders name type)
      apply case_returns program (typeEnvironment (.multiAbstractionNamed binders name type)) selected
        state state state (v "parameter") (encoded (parameterTerm (.multiAbstractionNamed binders name type)))
        multiBody _ _ typeCases (read_cases_encoded _) read _ _
      · simp [typeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, typeEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · exact multi_annotation_returns selected state binders name type
          (by simp [selected, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])
          (by simp [selected, typeEnvironment, Subst.lookup])

theorem parameter_type_returns (state : State) (parameter : TermParam) :
    PureReturns program [] state
      (a "gslt:premise:parameter-type" [encoded (parameterTerm parameter)]) state
      (typeResult (parameterType? parameter)) := by
  apply PureData.raw_authored_call_return program [] (typeEnvironment parameter) state state
    "gslt:premise:parameter-type" _ typeEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel)
  · intro index bounded
    have zero : index = 0 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    subst index
    decide +kernel
  · have clause := PureData.named_equation_clause program "gslt:premise:parameter-type"
        typeEquation ["parameter"] [encoded (parameterTerm parameter)]
        (by rfl) (by decide +kernel) (by decide) rfl
    simpa [typeEnvironment] using clause
  · exact type_body_returns state parameter

#print axioms parameter_type_returns

private def representationEquation : SpaceSemantics.Equation :=
  (equations "gslt:premise:parameter-representation")[0]'(by decide +kernel)
private def representationEnvironment (parameter : TermParam) (pattern : Pattern) : Subst :=
  [("pattern", patternValue pattern), ("parameter", encoded (parameterTerm parameter))]
private def singleRepresentationCases : SpaceSemantics.Cases :=
  [(a "PLam" [.symbol "BNone", v "body"], Effects.boolean true), (v "bad", Effects.boolean false)]
private def multiRepresentationCases : SpaceSemantics.Cases :=
  [(a "PMultiLam" [v "arity", .symbol "LNil", v "body"], Effects.boolean true),
   (v "bad", Effects.boolean false)]
private def singleRepresentationBody : Atom :=
  a "case" [v "pattern", .expression (singleRepresentationCases.map fun row => .expression [row.1, row.2])]
private def multiRepresentationBody : Atom :=
  a "case" [v "pattern", .expression (multiRepresentationCases.map fun row => .expression [row.1, row.2])]
private def representationCases : SpaceSemantics.Cases :=
  [(a "TermSimple" [v "name", v "type"], Effects.boolean true),
   (a "TermAbstraction" [v "binder", v "name", v "type"], singleRepresentationBody),
   (a "TermMultiAbstraction" [v "binders", v "name", v "type"], multiRepresentationBody),
   (v "bad", Effects.boolean false)]
private theorem representation_shape : representationEquation.body =
    a "case" [v "parameter", .expression (representationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def singleRepresentationEnvironment (caller : Subst) (pattern : Pattern) : Subst :=
  match pattern with
  | .lambda none body => ("body", patternValue body) :: caller
  | _ => ("bad", patternValue pattern) :: caller
private def multiRepresentationEnvironment (caller : Subst) (pattern : Pattern) : Subst :=
  match pattern with
  | .multiLambda arity [] body =>
      ("body", patternValue body) :: ("arity", encoded (.natural arity)) :: caller
  | _ => ("bad", patternValue pattern) :: caller

private theorem representation_symbol_match (caller : Subst) (head : String) (value : Atom) :
    SpaceSemantics.matchValue caller (.symbol head) value =
      if (.symbol head : Atom) = value then some caller else none :=
  SpaceSemantics.matchValue_literal (.symbol head) caller value

private theorem representation_variable_match (caller : Subst) (name : String) (value : Atom)
    (fresh : Subst.lookup caller name = none) :
    SpaceSemantics.matchValue caller (.var name) value = some ((name, value) :: caller) := by
  simp only [SpaceSemantics.matchValue, matchAtom, fresh]

private theorem representation_constructor_match (caller : Subst) (head : String)
    (patterns values : List Atom) (ordinary : head ≠ "cons") :
    SpaceSemantics.matchValue caller (a head patterns) (.expression values) =
      SpaceSemantics.matchValue.matchValues caller (.symbol head :: patterns) values := by
  apply SpaceSemantics.matchValue_expression_of_not_cons
  intro first rest same
  exact ordinary (by simpa using (List.cons.inj same).1)

private theorem single_representation_returns (caller : Subst) (state : State)
    (binder : Option String) (name : String) (type : TypeExpr) (pattern : Pattern)
    (stored : Subst.lookup caller "pattern" = some (patternValue pattern))
    (bodyFresh : Subst.lookup caller "body" = none)
    (badFresh : Subst.lookup caller "bad" = none) :
    PureReturns program caller state singleRepresentationBody state
      (Effects.boolean (matchesParameterRepresentation? (.abstractionNamed binder name type) pattern)) := by
  let selected := singleRepresentationEnvironment caller pattern
  apply case_returns program caller selected state state state (v "pattern") (patternValue pattern)
    (Effects.boolean (matchesParameterRepresentation? (.abstractionNamed binder name type) pattern))
    _ _ singleRepresentationCases (read_cases_encoded _) _ _ _
  · simpa [v, applySubst, stored] using variable_returns program caller state "pattern"
  · simp only [Subst.lookup] at bodyFresh badFresh
    cases pattern with
    | lambda binderName body =>
      cases binderName with
      | none => simp [singleRepresentationCases, selected, singleRepresentationEnvironment,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues,
          representation_constructor_match, representation_symbol_match, representation_variable_match,
          InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          Subst.lookup, matchesParameterRepresentation?, Effects.boolean, bodyFresh,
          a, v, patternValue, encoded]
      | some binderName => simp [singleRepresentationCases, selected, singleRepresentationEnvironment,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues,
          representation_constructor_match, representation_symbol_match, representation_variable_match,
          InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup,
          matchesParameterRepresentation?, Effects.boolean, badFresh, a, v, patternValue, encoded]
    | _ => simp [singleRepresentationCases, selected, singleRepresentationEnvironment,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues,
        representation_constructor_match, representation_symbol_match, representation_variable_match, InferenceCettaWire.encodePattern,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup,
        matchesParameterRepresentation?, Effects.boolean, badFresh,
        a, v, patternValue, encoded]
  · exact grounded_returns program selected state
      (.bool (matchesParameterRepresentation? (.abstractionNamed binder name type) pattern))

private theorem multi_representation_returns (caller : Subst) (state : State)
    (binders : List String) (name : String) (type : TypeExpr) (pattern : Pattern)
    (stored : Subst.lookup caller "pattern" = some (patternValue pattern))
    (arityFresh : Subst.lookup caller "arity" = none)
    (bodyFresh : Subst.lookup caller "body" = none)
    (badFresh : Subst.lookup caller "bad" = none) :
    PureReturns program caller state multiRepresentationBody state
      (Effects.boolean (matchesParameterRepresentation? (.multiAbstractionNamed binders name type) pattern)) := by
  let selected := multiRepresentationEnvironment caller pattern
  apply case_returns program caller selected state state state (v "pattern") (patternValue pattern)
    (Effects.boolean (matchesParameterRepresentation? (.multiAbstractionNamed binders name type) pattern))
    _ _ multiRepresentationCases (read_cases_encoded _) _ _ _
  · simpa [v, applySubst, stored] using variable_returns program caller state "pattern"
  · simp only [Subst.lookup] at arityFresh bodyFresh badFresh
    cases pattern with
    | multiLambda arity names body => cases names <;> simp [multiRepresentationCases, selected, multiRepresentationEnvironment,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues,
        representation_constructor_match, representation_symbol_match, representation_variable_match, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodeList, CettaWire.encodeList,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup,
        matchesParameterRepresentation?, Effects.boolean, arityFresh, bodyFresh, badFresh,
        a, v, patternValue, encoded]
    | _ => simp [multiRepresentationCases, selected, multiRepresentationEnvironment,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues,
        representation_constructor_match, representation_symbol_match, representation_variable_match, InferenceCettaWire.encodePattern, InferenceCettaWire.encodeBinder,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup,
        matchesParameterRepresentation?, Effects.boolean, badFresh,
        a, v, patternValue, encoded]
  · exact grounded_returns program selected state
      (.bool (matchesParameterRepresentation? (.multiAbstractionNamed binders name type) pattern))

private theorem representation_body_returns (state : State) (parameter : TermParam) (pattern : Pattern) :
    PureReturns program (representationEnvironment parameter pattern) state representationEquation.body state
      (Effects.boolean (matchesParameterRepresentation? parameter pattern)) := by
  rw [representation_shape]
  have read : PureReturns program (representationEnvironment parameter pattern) state (v "parameter") state
      (encoded (parameterTerm parameter)) := by
    simpa [v, representationEnvironment, applySubst, Subst.lookup] using
      variable_returns program (representationEnvironment parameter pattern) state "parameter"
  cases parameter with
  | simple name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        representationEnvironment (.simple name type) pattern
      apply case_returns program (representationEnvironment (.simple name type) pattern) selected state state state
        (v "parameter") (encoded (parameterTerm (.simple name type))) (Effects.boolean true)
        _ _ representationCases (read_cases_encoded _) read _ _
      · simp [representationCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, representationEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · simpa [matchesParameterRepresentation?, Effects.boolean] using grounded_returns program selected state (.bool true)
  | abstractionNamed binder name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        ("binder", encoded (InferenceCettaWire.encodeBinder binder)) ::
        representationEnvironment (.abstractionNamed binder name type) pattern
      apply case_returns program (representationEnvironment (.abstractionNamed binder name type) pattern) selected
        state state state (v "parameter") (encoded (parameterTerm (.abstractionNamed binder name type)))
        singleRepresentationBody _ _ representationCases (read_cases_encoded _) read _ _
      · simp [representationCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, representationEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · exact single_representation_returns selected state binder name type pattern
          (by simp [selected, representationEnvironment, Subst.lookup])
          (by simp [selected, representationEnvironment, Subst.lookup])
          (by simp [selected, representationEnvironment, Subst.lookup])
  | multiAbstractionNamed binders name type =>
      let selected := ("type", typeValue type) :: ("name", encoded (.string name)) ::
        ("binders", encoded (encodeList Term.string binders)) ::
        representationEnvironment (.multiAbstractionNamed binders name type) pattern
      apply case_returns program (representationEnvironment (.multiAbstractionNamed binders name type) pattern) selected
        state state state (v "parameter") (encoded (parameterTerm (.multiAbstractionNamed binders name type)))
        multiRepresentationBody _ _ representationCases (read_cases_encoded _) read _ _
      · simp [representationCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, representationEnvironment, parameterTerm,
          typeValue, CettaWireAtom.encode, CettaWireAtom.encodeMany, selected, Subst.lookup]
      · exact multi_representation_returns selected state binders name type pattern
          (by simp [selected, representationEnvironment, Subst.lookup])
          (by simp [selected, representationEnvironment, Subst.lookup])
          (by simp [selected, representationEnvironment, Subst.lookup])
          (by simp [selected, representationEnvironment, Subst.lookup])

theorem parameter_representation_returns (state : State) (parameter : TermParam) (pattern : Pattern) :
    PureReturns program [] state
      (a "gslt:premise:parameter-representation" [encoded (parameterTerm parameter), patternValue pattern]) state
      (Effects.boolean (matchesParameterRepresentation? parameter pattern)) := by
  apply PureData.raw_authored_call_return program [] (representationEnvironment parameter pattern) state state
    "gslt:premise:parameter-representation" _ representationEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel)
  · intro index bounded
    have choices : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases choices with rfl | rfl <;> decide +kernel
  · have clause := PureData.named_equation_clause program "gslt:premise:parameter-representation"
        representationEquation ["parameter", "pattern"] [encoded (parameterTerm parameter), patternValue pattern]
        (by rfl) (by decide +kernel) (by decide) rfl
    simpa [representationEnvironment] using clause
  · exact representation_body_returns state parameter pattern

#print axioms parameter_representation_returns


/-- Caller syntax supplies the same raw parameter datum as the closed call. -/
theorem parameter_type_captured_returns (caller : Subst) (state : State)
    (parameter : TermParam) (expression : Atom)
    (captured : applySubst caller expression = encoded (parameterTerm parameter)) :
    PureReturns program caller state (a "gslt:premise:parameter-type" [expression]) state
      (typeResult (parameterType? parameter)) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:premise:parameter-type"
    [encoded (parameterTerm parameter)] [expression] _
    (by decide +kernel) _ (by decide) _ (parameter_type_returns state parameter)
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst index
    decide +kernel
  · simp only [List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode, captured]

/-- Captured pattern bodies remain opaque during representation inspection. -/
theorem parameter_representation_captured_returns (caller : Subst) (state : State)
    (parameter : TermParam) (pattern : Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [encoded (parameterTerm parameter), patternValue pattern]) :
    PureReturns program caller state (a "gslt:premise:parameter-representation" [one, two]) state
      (Effects.boolean (matchesParameterRepresentation? parameter pattern)) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:premise:parameter-representation"
    [encoded (parameterTerm parameter), patternValue pattern] [one, two] _
    (by decide +kernel) _ (by decide) _ (parameter_representation_returns state parameter pattern)
  · intro index bounded
    have choices : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases choices with rfl | rfl <;> decide +kernel
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

#print axioms parameter_type_captured_returns
#print axioms parameter_representation_captured_returns

end TypedParameters


open Mettapedia.OSLF.MeTTaIL

namespace Controls

/-- Shared retained-source controls use the existing carriers exclusively. -/
inductive Input where
  | freeVariables (pattern : Pattern)
  | freeVariablesList (patterns : List Pattern)
  | fresh (name : String) (pattern : Pattern)
  | resolveName (name : String) (bindings : Bindings)
  | freshness (name : String) (plan : PatternPlan) (bindings : Bindings)

  | scopeRemove (parameter : String) (assignment : ScopedRuleMatching.Assignment)
  | scopeBind (parameter : String) (value : RuleBinding.ContextualValue) (assignment : ScopedRuleMatching.Assignment)
  | scopeRestore (parameter : String) (initial final : ScopedRuleMatching.Assignment)
  | scopeLocalValue (bound : List TypeExpr) (pattern : Pattern)
  | scopeCollection (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) (name : String)

  | parameterType (parameter : TermParam)
  | parameterRepresentation (parameter : TermParam) (pattern : Pattern)

def language : LanguageDef := LanguageDef.empty "CanonicalPremiseOperations"

def Input.queryTerm : Input → Term
  | .freeVariables pattern => .application "gslt:premise:free-vars" [InferenceCettaWire.encodePattern pattern]
  | .freeVariablesList patterns => .application "gslt:premise:free-vars-list" [InferenceCettaWire.encodePatterns patterns]
  | .fresh name pattern => .application "if"
      [.application "gslt:premise:fresh" [.string name, InferenceCettaWire.encodePattern pattern],
        .symbol "FreshYes", .symbol "FreshNo"]
  | .resolveName name bindings => .application "gslt:premise:resolve-name"
      [.string name, MatchAutomataBindingExecution.bindingsTerm bindings]
  | .freshness name plan bindings => .application "gslt:premise:freshness"
      [.string name, InferenceCettaWire.encodePattern plan.erase, MatchAutomataBindingExecution.bindingsTerm bindings]

  | .scopeRemove parameter assignment => .application "gslt:premise:scope-remove"
      [.string parameter, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment]
  | .scopeBind parameter value assignment => .application "gslt:premise:scope-bind"
      [.string parameter, InferenceCettaWire.AuthoredRule.contextualValueTerm value,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment]
  | .scopeRestore parameter initial final => .application "gslt:premise:scope-restore"
      [.string parameter, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm initial,
        RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm final]
  | .scopeLocalValue bound pattern => .application "gslt:premise:scope-local-value"
      [.natural bound.length, InferenceCettaWire.encodePattern pattern]
  | .scopeCollection ambient assignment name => .application "gslt:premise:scope-collection"
      [.natural ambient, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment, .string name]

  | .parameterType parameter => .application "gslt:premise:parameter-type"
      [InferenceCettaWire.AuthoredRule.parameterTerm parameter]
  | .parameterRepresentation parameter pattern => .application "if"
      [.application "gslt:premise:parameter-representation"
        [InferenceCettaWire.AuthoredRule.parameterTerm parameter, InferenceCettaWire.encodePattern pattern],
        .symbol "RepresentationYes", .symbol "RepresentationNo"]

def Input.expectedTerm : Input → Term
  | .freeVariables pattern => RelationPremiseExecution.namesTerm
      (Mettapedia.OSLF.MeTTaIL.Substitution.freeVars pattern)
  | .freeVariablesList patterns => RelationPremiseExecution.namesTerm
      (patterns.flatMap Mettapedia.OSLF.MeTTaIL.Substitution.freeVars)
  | .fresh name pattern => if Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern
      then .symbol "FreshYes" else .symbol "FreshNo"
  | .resolveName name bindings => nameOptionTerm (match bindings.lookup name with
      | none => some name
      | some (.fvar resolved) => some resolved
      | some _ => none)
  | .freshness name plan bindings => RelationPremiseExecution.bindingResultsTerm
      (Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language bindings
          (.freshness {varName := name, term := plan.erase}))

  | .scopeRemove parameter assignment => RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
      (GeneralPremise.removeParameter parameter assignment)
  | .scopeBind parameter value assignment => RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
      (GeneralPremise.bindParameter parameter value assignment)
  | .scopeRestore parameter initial final => RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
      (GeneralPremise.restoreParameter parameter initial final)
  | .scopeLocalValue bound pattern => InferenceCettaWire.AuthoredRule.contextualValueTerm
      (GeneralPremise.localValue bound pattern)
  | .scopeCollection ambient assignment name => QuantifiedLocal.finiteCollectionOptionTerm
      (GeneralPremise.finiteCollection? ambient assignment name)

  | .parameterType parameter => CettaWire.encodeOption InferenceCettaWire.AuthoredRule.typeTerm
      (Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter)
  | .parameterRepresentation parameter pattern =>
      if Mettapedia.GSLT.LanguageDef.WellSorted.matchesParameterRepresentation? parameter pattern
      then .symbol "RepresentationYes" else .symbol "RepresentationNo"

theorem Input.returns (input : Input) (state : State) :
    PureReturns program [] state (encoded input.queryTerm) state (encoded input.expectedTerm) := by
  cases input with
  | freeVariables pattern =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        free_vars_returns state pattern
  | freeVariablesList patterns =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        free_vars_list_returns state patterns
  | fresh name pattern =>
      change PureReturns program [] state (a "if"
        [a "gslt:premise:fresh" [encoded (.string name), patternValue pattern],
          .symbol "FreshYes", .symbol "FreshNo"]) state _
      apply if_returns program [] state state state _
        (Effects.boolean (Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern))
        (.symbol "FreshYes") (.symbol "FreshNo") _ (fresh_returns state name pattern)
      cases fresh : Mettapedia.OSLF.MeTTaIL.Substitution.isFresh name pattern with
      | false =>
          rw [show (Effects.boolean false == Effects.boolean true) = false from by decide +kernel]
          simpa only [Input.expectedTerm, fresh, Bool.false_eq_true, ite_false, CettaWireAtom.encode] using
            symbol_returns program [] state "FreshNo"
      | true =>
          rw [show (Effects.boolean true == Effects.boolean true) = true from by decide +kernel]
          simpa only [Input.expectedTerm, fresh, ite_true, CettaWireAtom.encode] using
            symbol_returns program [] state "FreshYes"
  | resolveName name bindings =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        resolve_name_returns state name bindings
  | freshness name plan bindings =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        freshness_returns state Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty language name plan bindings

  | scopeRemove parameter assignment =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        QuantifiedLocal.remove_parameter_returns state parameter assignment
  | scopeBind parameter value assignment =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        QuantifiedLocal.bind_parameter_returns state parameter value assignment
  | scopeRestore parameter initial final =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        QuantifiedLocal.restore_parameter_returns state parameter initial final
  | scopeLocalValue bound pattern =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        QuantifiedLocal.local_value_returns state bound pattern
  | scopeCollection ambient assignment name =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        QuantifiedLocal.finite_collection_returns state ambient assignment name

  | parameterType parameter =>
      simpa only [Input.queryTerm, Input.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        TypedParameters.typeResult] using TypedParameters.parameter_type_returns state parameter
  | parameterRepresentation parameter pattern =>
      change PureReturns program [] state (a "if"
        [a "gslt:premise:parameter-representation"
          [encoded (InferenceCettaWire.AuthoredRule.parameterTerm parameter), patternValue pattern],
          .symbol "RepresentationYes", .symbol "RepresentationNo"]) state _
      apply QuantifiedLocal.bool_if_returns [] state _
        (Mettapedia.GSLT.LanguageDef.WellSorted.matchesParameterRepresentation? parameter pattern)
        _ _ _ (TypedParameters.parameter_representation_returns state parameter pattern)
      cases checked : Mettapedia.GSLT.LanguageDef.WellSorted.matchesParameterRepresentation? parameter pattern with
      | false =>
          simpa only [Input.expectedTerm, checked, Bool.false_eq_true, ite_false, CettaWireAtom.encode] using
            symbol_returns program [] state "RepresentationNo"
      | true =>
          simpa only [Input.expectedTerm, checked, ite_true, CettaWireAtom.encode] using
            symbol_returns program [] state "RepresentationYes"

structure Fixture where
  name : String
  input : Input

def Fixture.queryTerm (fixture : Fixture) : Term := fixture.input.queryTerm
def Fixture.expectedTerm (fixture : Fixture) : Term := fixture.input.expectedTerm

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (encoded fixture.queryTerm) state (encoded fixture.expectedTerm) :=
  fixture.input.returns state

private def localCapture (ambient : Nat) (pattern : Pattern) : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue :=
  ⟨[], ambient, pattern⟩
private def collectionCapture (ambient : Nat) (kind : CollType) (elements : List Pattern)
    (rest : Option String) : Mettapedia.OSLF.MeTTaIL.RuleBinding.ContextualValue :=
  localCapture ambient (.collection kind elements rest)

def lexicalFixtures : List Fixture :=
  [⟨"lexical-remove-all-shadowed-entries", .scopeRemove "x"
     [("x", localCapture 1 (.bvar 0)), ("y", localCapture 1 (.fvar "saved")),
      ("x", localCapture 1 (.fvar "older"))]⟩,
   ⟨"lexical-remove-retains-other-duplicates", .scopeRemove "absent"
     [("y", localCapture 0 (.fvar "first")), ("y", localCapture 0 (.fvar "later"))]⟩,
   ⟨"lexical-bind-shadows-outer", .scopeBind "x" (localCapture 1 (.bvar 0))
     [("x", localCapture 1 (.fvar "old"))]⟩,
   ⟨"lexical-restore-outer-retains-body-output", .scopeRestore "x"
     [("x", localCapture 1 (.fvar "outer"))]
     [("x", localCapture 1 (.fvar "local")), ("result", localCapture 1 (.fvar "output"))]⟩,
   ⟨"lexical-restore-unbound-retains-body-output", .scopeRestore "x" []
     [("x", localCapture 1 (.fvar "local")), ("result", localCapture 1 (.fvar "output"))]⟩,
   ⟨"lexical-restore-first-outer-capture", .scopeRestore "x"
     [("x", localCapture 0 (.fvar "first")), ("x", localCapture 0 (.fvar "later"))]
     [("x", localCapture 0 (.fvar "local"))]⟩,
   ⟨"lexical-local-value-retains-open-ambient", .scopeLocalValue [.base "A"] (.bvar 0)⟩,
   ⟨"lexical-local-value-retains-opaque-body", .scopeLocalValue []
     (.lambda none (.apply "print!" [.bvar 0]))⟩,
   ⟨"quantifier-collection-missing-is-refused", .scopeCollection 0 [] "xs"⟩,
   ⟨"quantifier-empty-collection-is-successful", .scopeCollection 0
     [("xs", collectionCapture 0 .vec [] none)] "xs"⟩,
   ⟨"quantifier-collection-retains-order-and-duplicates", .scopeCollection 0
     [("xs", collectionCapture 0 .vec [.fvar "second", .fvar "first", .fvar "second"] none)] "xs"⟩,
   ⟨"quantifier-collection-retains-bag-tag", .scopeCollection 0
     [("xs", collectionCapture 0 .hashBag [.fvar "a", .fvar "a"] none)] "xs"⟩,
   ⟨"quantifier-collection-retains-set-tag", .scopeCollection 0
     [("xs", collectionCapture 0 .hashSet [.fvar "a"] none)] "xs"⟩,
   ⟨"quantifier-collection-retains-open-ambient", .scopeCollection 1
     [("xs", collectionCapture 1 .vec [.bvar 0] none)] "xs"⟩,
   ⟨"quantifier-collection-wrong-ambient-refused", .scopeCollection 0
     [("xs", collectionCapture 1 .vec [] none)] "xs"⟩,
   ⟨"quantifier-collection-wrong-arity-refused", .scopeCollection 0
     [("xs", ⟨[.base "A"], 0, .collection .vec [] none⟩)] "xs"⟩,
   ⟨"quantifier-collection-ill-scoped-refused", .scopeCollection 0
     [("xs", collectionCapture 0 .vec [.bvar 0] none)] "xs"⟩,
   ⟨"quantifier-collection-open-rest-refused", .scopeCollection 0
     [("xs", collectionCapture 0 .vec [] (some "tail"))] "xs"⟩,
   ⟨"quantifier-non-collection-refused", .scopeCollection 0
     [("xs", localCapture 0 (.fvar "atom"))] "xs"⟩]

def lexicalIncorrectResults : List (Fixture × Term) :=
  [(⟨"unresolved-rest-cannot-become-empty-success", .scopeCollection 0
      [("xs", collectionCapture 0 .vec [] (some "tail"))] "xs"⟩,
      QuantifiedLocal.finiteCollectionOptionTerm (some (.vec, []))),
   (⟨"concrete-empty-collection-cannot-be-refused", .scopeCollection 0
      [("xs", collectionCapture 0 .vec [] none)] "xs"⟩, .symbol "None"),
   (⟨"lexical-body-parameter-cannot-escape", .scopeRestore "x"
      [("x", localCapture 0 (.fvar "outer"))] [("x", localCapture 0 (.fvar "local"))]⟩,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm
        [("x", localCapture 0 (.fvar "local"))])]

/-- Empty quantification is successful only after the actual finite collection
has been read; unreadable collection data is a separate refusal. -/
theorem concrete_empty_is_not_refusal :
    GeneralPremise.finiteCollection? 0 [("xs", collectionCapture 0 .vec [] none)] "xs" = some (.vec, []) ∧
    GeneralPremise.finiteCollection? 0 [("xs", collectionCapture 0 .vec [] (some "rest"))] "xs" = none := by
  decide +kernel

theorem lexical_restoration_preserves_output :
    GeneralPremise.restoreParameter "x" [("x", localCapture 1 (.fvar "outer"))]
      [("x", localCapture 1 (.fvar "local")), ("out", localCapture 1 (.bvar 0))] =
        [("x", localCapture 1 (.fvar "outer")), ("out", localCapture 1 (.bvar 0))] := by
  decide +kernel

private def typeA : TypeExpr := .base "A"
private def typeB : TypeExpr := .base "B"
private def simpleA : TermParam := .simple "argument" typeA
private def singleA : TermParam := .abstractionNamed (some "displayed") "body" typeA
private def multiA : TermParam := .multiAbstractionNamed ["first", "second"] "body" typeA

def typedParameterFixtures : List Fixture :=
  [⟨"parameter-simple-base", .parameterType simpleA⟩,
   ⟨"parameter-simple-arrow", .parameterType (.simple "f" (.arrow typeA typeB))⟩,
   ⟨"parameter-simple-multi-domain", .parameterType (.simple "xs" (.multiBinder typeA))⟩,
   ⟨"parameter-simple-collection", .parameterType (.simple "xs" (.collection .vec typeA))⟩,
   ⟨"parameter-single-base", .parameterType singleA⟩,
   ⟨"parameter-single-arrow", .parameterType (.abstractionNamed none "body" (.arrow typeA typeB))⟩,
   ⟨"parameter-single-multi-domain-refused", .parameterType (.abstractionNamed none "body" (.multiBinder typeA))⟩,
   ⟨"parameter-single-collection-refused", .parameterType (.abstractionNamed none "body" (.collection .vec typeA))⟩,
   ⟨"parameter-multi-base", .parameterType multiA⟩,
   ⟨"parameter-multi-arrow", .parameterType (.multiAbstractionNamed [] "body" (.arrow (.multiBinder typeA) typeB))⟩,
   ⟨"parameter-multi-single-domain-refused", .parameterType (.multiAbstractionNamed [] "body" (.arrow typeA typeB))⟩,
   ⟨"parameter-multi-collection-refused", .parameterType (.multiAbstractionNamed [] "body" (.collection .vec typeA))⟩,
   ⟨"representation-simple-open-variable", .parameterRepresentation simpleA (.bvar 0)⟩,
   ⟨"representation-simple-free-variable", .parameterRepresentation simpleA (.fvar "x")⟩,
   ⟨"representation-simple-lambda", .parameterRepresentation simpleA (.lambda (some "x") (.bvar 0))⟩,
   ⟨"representation-simple-collection", .parameterRepresentation simpleA (.collection .vec [] (some "rest"))⟩,
   ⟨"representation-single-nameless", .parameterRepresentation singleA (.lambda none (.bvar 0))⟩,
   ⟨"representation-single-named-refused", .parameterRepresentation singleA (.lambda (some "displayed") (.bvar 0))⟩,
   ⟨"representation-single-ordinary-refused", .parameterRepresentation singleA (.apply "f" [])⟩,
   ⟨"representation-single-vector-refused", .parameterRepresentation singleA (.collection .vec [] none)⟩,
   ⟨"representation-multi-empty-nameless", .parameterRepresentation multiA (.multiLambda 0 [] (.apply "value" []))⟩,
   ⟨"representation-multi-two-nameless", .parameterRepresentation multiA (.multiLambda 2 [] (.bvar 1))⟩,
   ⟨"representation-multi-named-refused", .parameterRepresentation multiA (.multiLambda 2 ["first", "second"] (.bvar 1))⟩,
   ⟨"representation-multi-single-refused", .parameterRepresentation multiA (.lambda none (.bvar 0))⟩]

def typedParameterIncorrectResults : List (Fixture × Term) :=
  [(typedParameterFixtures[0]'(by decide +kernel), .symbol "None"),
   (typedParameterFixtures[6]'(by decide +kernel), .application "Some" [InferenceCettaWire.AuthoredRule.typeTerm typeA]),
   (typedParameterFixtures[16]'(by decide +kernel), .symbol "RepresentationNo"),
   (typedParameterFixtures[17]'(by decide +kernel), .symbol "RepresentationYes")]

def fixtures : List Fixture :=
  [⟨"bound-index-is-not-free", .freeVariables (.bvar 7)⟩,
   ⟨"single-free-variable", .freeVariables (.fvar "atom")⟩,
   ⟨"application-occurrences-retain-order-and-duplicates", .freeVariables
     (.apply "tuple" [.fvar "right", .fvar "left", .fvar "right"])⟩,
   ⟨"binder-display-name-is-not-a-free-occurrence", .freeVariables
     (.lambda (some "display") (.apply "body" [.bvar 0, .fvar "atom"]))⟩,
   ⟨"anonymous-binder-retains-body-occurrences", .freeVariables (.lambda none (.fvar "atom"))⟩,
   ⟨"multibinder-display-names-are-not-occurrences", .freeVariables
     (.multiLambda 2 ["left", "right"] (.apply "body" [.fvar "atom", .bvar 1]))⟩,
   ⟨"substitution-body-and-replacement-are-scanned-in-order", .freeVariables
     (.subst (.apply "body" [.fvar "left", .fvar "same"]) (.apply "value" [.fvar "right", .fvar "same"]))⟩,
   ⟨"vector-rest-metadata-is-not-an-occurrence", .freeVariables
     (.collection .vec [.fvar "element", .fvar "element"] (some "rest"))⟩,
   ⟨"bag-occurrences-retain-duplicates", .freeVariables
     (.collection .hashBag [.fvar "atom", .fvar "atom"] none)⟩,
   ⟨"set-tag-does-not-deduplicate-free-variable-occurrences", .freeVariables
     (.collection .hashSet [.fvar "atom", .fvar "atom"] none)⟩,
   ⟨"empty-pattern-list", .freeVariablesList []⟩,
   ⟨"ordered-pattern-list", .freeVariablesList [.fvar "first", .bvar 2, .fvar "last", .fvar "first"]⟩,
   ⟨"fresh-display-name", .fresh "display" (.lambda (some "display") (.fvar "body"))⟩,
   ⟨"nonfresh-body-name", .fresh "body" (.lambda (some "display") (.fvar "body"))⟩,
   ⟨"fresh-rest-metadata-name", .fresh "rest" (.collection .vec [.fvar "element"] (some "rest"))⟩,
   ⟨"nonfresh-substitution-replacement", .fresh "replacement" (.subst (.bvar 0) (.fvar "replacement"))⟩,
   ⟨"absent-name-capture-retains-literal", .resolveName "name" []⟩,
   ⟨"name-capture-resolves", .resolveName "name" [("name", .fvar "actual")]⟩,
   ⟨"name-lookup-retains-first-binding", .resolveName "name"
     [("name", .fvar "first"), ("name", .fvar "later")]⟩,
   ⟨"non-name-application-capture-refused", .resolveName "name" [("name", .apply "actual" [])]⟩,
   ⟨"non-name-binder-capture-refused", .resolveName "name" [("name", .lambda none (.fvar "actual"))]⟩,
   ⟨"freshness-with-absent-name-and-term-captures", .freshness "atom" (.metavariable "body") []⟩,
   ⟨"retained-unbound-variable-can-refuse-freshness", .freshness "body" (.metavariable "body") []⟩,
   ⟨"freshness-checks-instantiated-term", .freshness "atom" (.metavariable "body") [("body", .fvar "atom")]⟩,
   ⟨"resolved-name-can-be-fresh", .freshness "name" (.metavariable "body")
     [("name", .fvar "actual"), ("body", .fvar "other")]⟩,
   ⟨"resolved-name-can-refuse-freshness", .freshness "name" (.metavariable "body")
     [("name", .fvar "actual"), ("body", .fvar "actual")]⟩,
   ⟨"non-name-capture-refuses-freshness", .freshness "name" (.metavariable "body")
     [("name", .bvar 0), ("body", .fvar "other")]⟩,
   ⟨"full-pattern-payload-can-satisfy-freshness", .freshness "display" (.metavariable "body")
     [("body", .lambda (some "display") (.fvar "other"))]⟩,
   ⟨"full-pattern-payload-can-refuse-freshness", .freshness "atom" (.metavariable "body")
     [("body", .multiLambda 1 ["display"] (.fvar "atom"))]⟩,
   ⟨"captured-collections-use-canonical-free-vars", .freshness "rest" (.metavariable "body")
     [("body", .collection .vec [.fvar "other"] (some "rest"))]⟩,
   ⟨"freshness-retains-the-entire-original-binding-list", .freshness "atom" (.application "unit" [])
     [("body", .fvar "first"), ("body", .fvar "later"), ("unused", .lambda none (.bvar 0))]⟩] ++ lexicalFixtures ++ typedParameterFixtures

def incorrectResults : List (Fixture × Term) :=
  [(⟨"free-variable-duplicates-cannot-be-erased", .freeVariables (.apply "pair" [.fvar "atom", .fvar "atom"])⟩,
      RelationPremiseExecution.namesTerm ["atom"]),
   (⟨"display-metadata-cannot-be-counted-as-free", .freeVariables (.lambda (some "display") (.fvar "body"))⟩,
      RelationPremiseExecution.namesTerm ["display", "body"]),
   (⟨"non-name-capture-cannot-retain-literal-name", .resolveName "name" [("name", .apply "actual" [])]⟩,
      nameOptionTerm (some "name")),
   (⟨"post-substitution-nonfreshness-cannot-succeed", .freshness "atom" (.metavariable "body")
      [("body", .fvar "atom")]⟩, RelationPremiseExecution.bindingResultsTerm [[("body", .fvar "atom")]])] ++ lexicalIncorrectResults ++ typedParameterIncorrectResults

theorem Fixture.completed_iff (fixture : Fixture) (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate [] (encoded fixture.queryTerm)} =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded fixture.expectedTerm] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (fixture.returns state) after answers input output

theorem Fixture.derivation_iff (fixture : Fixture) (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state, control := .evaluate [] (encoded fixture.queryTerm)}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded fixture.expectedTerm] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (fixture.returns state) after answers input output

theorem Fixture.incorrect_derivation_refused (fixture : Fixture) (incorrect : Term)
    (different : incorrect ≠ fixture.expectedTerm) (state : State) :
    ¬ DeclarativeSpec.Runs program {state, control := .evaluate [] (encoded fixture.queryTerm)}
      (.complete state [encoded incorrect] [] []) := by
  intro returned
  have result := (fixture.derivation_iff state state _ [] []).mp returned
  have same := (List.cons.inj result.2.1).1
  exact different (CettaWireAtom.encode_injective incorrect fixture.expectedTerm same)

theorem incorrect_results_refused (state : State) :
    ∀ test ∈ incorrectResults,
      ¬ DeclarativeSpec.Runs program {state, control := .evaluate [] (encoded test.1.queryTerm)}
        (.complete state [encoded test.2] [] []) := by
  have different : ∀ test ∈ incorrectResults, test.2 ≠ test.1.expectedTerm := by decide +kernel
  intro test member
  exact test.1.incorrect_derivation_refused test.2 (different test member) state

end Controls

#print axioms free_vars_returns
#print axioms free_vars_captured_returns
#print axioms free_vars_list_returns
#print axioms fresh_captured_returns
#print axioms fresh_returns
#print axioms resolve_name_captured_returns
#print axioms resolve_name_returns
#print axioms freshness_captured_returns
#print axioms freshness_returns
#print axioms freshness_completed_iff
#print axioms freshness_derivation_iff
#print axioms Controls.Fixture.returns
#print axioms Controls.Fixture.derivation_iff
#print axioms Controls.incorrect_results_refused

open Mettapedia.OSLF.MeTTaIL

/-! ## Whole-pattern declaration-derived checking -/
namespace DeclarationTyping

open Mettapedia.GSLT.LanguageDef.WellSorted
open InferenceCettaWire.AuthoredRule

/-- Exact fields inspected by typing; this projection does not encode printing
or evaluation policies of the authored declaration. -/
def declarationsTerm (declarations : List GrammarRule) : Term :=
  encodeList typingDeclarationTerm declarations

/-- The existing first-match context is carried by the shared payload bindings. -/
def freeContextTerm (context : List (String × TypeExpr)) : Term :=
  MatchAutomataBindingExecution.payloadBindingsTerm
    (context.map fun entry => (entry.1, typeTerm entry.2))

def boundContextTerm (context : List TypeExpr) : Term := encodeList typeTerm context

private abbrev typeValue (type : TypeExpr) : Atom := encoded (typeTerm type)
private abbrev declarationsValue (declarations : List GrammarRule) : Atom := encoded (declarationsTerm declarations)
private abbrev freeValue (context : List (String × TypeExpr)) : Atom := encoded (freeContextTerm context)
private abbrev boundValue (context : List TypeExpr) : Atom := encoded (boundContextTerm context)
private abbrev parametersValue (parameters : List TermParam) : Atom := encoded (encodeList parameterTerm parameters)

private inductive RawHelper where | has | arguments | elements | constructors | collections | open
private abbrev RawHelper.head : RawHelper → String
  | .has => "gslt:premise:type-has"
  | .arguments => "gslt:premise:type-arguments"
  | .elements => "gslt:premise:type-elements"
  | .constructors => "gslt:premise:type-constructors"
  | .collections => "gslt:premise:type-collection-declarations"
  | .open => "gslt:premise:open-well-sorted"
private def RawHelper.names : RawHelper → List String
  | .has => ["declarations", "free", "bound", "pattern", "expected"]
  | .arguments => ["declarations", "free", "bound", "arguments", "parameters"]
  | .elements => ["declarations", "free", "bound", "elements", "element"]
  | .constructors => ["declarations", "free", "bound", "label", "arguments", "expected", "remaining"]
  | .collections => ["declarations", "free", "bound", "kind", "elements", "expected", "remaining"]
  | .open => ["declarations", "free", "bound", "expected", "pattern"]
private def rawEquation (helper : RawHelper) : SpaceSemantics.Equation :=
  ((RuleExecutionProgram.premiseSource.program.equations.filter
    (fun equation => equation.head == helper.head))[0]'(by cases helper <;> decide +kernel))
private def rawEnvironment (helper : RawHelper) (values : List Atom) : Subst :=
  ((helper.names.zip values).reverse)

private theorem raw_clause (helper : RawHelper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values =
      [.evaluate (rawEnvironment helper values) (rawEquation helper).body] :=
  PureData.named_equation_clause program helper.head (rawEquation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

set_option maxHeartbeats 800000 in
private theorem raw_arguments (helper : RawHelper) (index : Nat)
    (bounded : index < helper.names.length) : argumentIsRaw program helper.head index = true := by
  cases helper <;> simp only [RawHelper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | decide +kernel

private theorem raw_call (helper : RawHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (rawEnvironment helper values) state (rawEquation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (rawEnvironment helper values) state state
    helper.head arguments (rawEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply raw_arguments helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact raw_clause helper values length
  · exact returned

private theorem raw_closed (helper : RawHelper) (state : State) (values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (returned : PureReturns program (rawEnvironment helper values) state (rawEquation helper).body state answer) :
    PureReturns program [] state (a helper.head values) state answer :=
  raw_call helper [] state values values answer length (by
    have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    rw [unchanged]; exact List.map_id values) returned

private theorem raw_capture (helper : RawHelper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact raw_arguments helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

private theorem typeTerm_injective : Function.Injective typeTerm := by
  intro first second same
  have decoded := congrArg decodeType? same
  simpa only [decodeType?_typeTerm, Option.some.injEq] using decoded

private theorem typeOption_injective : Function.Injective (CettaWire.encodeOption typeTerm) := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [CettaWire.encodeOption, typeTerm_injective.eq_iff]

private theorem payload_free_lookup (context : List (String × TypeExpr)) (name : String) :
    MatchAutomataBindingExecution.payloadLookup (context.map fun entry => (entry.1, typeTerm entry.2)) name =
      (FreeTypeContext.ofList context name).map typeTerm := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, sort⟩
      by_cases same : key = name
      · subst key
        simp [MatchAutomataBindingExecution.payloadLookup, FreeTypeContext.ofList]
      · have different : (key == name) = false := by simp [same]
        simp only [List.map_cons, MatchAutomataBindingExecution.payloadLookup,
          List.find?_cons, different, FreeTypeContext.ofList, same, ite_false] at ih ⊢
        exact ih

private theorem payload_option_type (value : Option TypeExpr) :
    MatchAutomataBindingExecution.payloadOptionTerm (value.map typeTerm) =
      CettaWire.encodeOption typeTerm value := by cases value <;> rfl

private theorem free_lookup_returns (caller : Subst) (state : State)
    (context : List (String × TypeExpr)) (name : String) (one two : String)
    (captured : [v one, v two].map (applySubst caller) = [encoded (.string name), freeValue context]) :
    PureReturns program caller state (a "gslt:automata:binding" [v one, v two]) state
      (encoded (CettaWire.encodeOption typeTerm (FreeTypeContext.ofList context name))) := by
  apply RuleExecutionProgram.automata_captured_returns
    (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
  have looked := MatchAutomataBindingExecution.payload_binding_captured_returns caller state name
    (context.map fun (entry : String × TypeExpr) => (entry.1, typeTerm entry.2)) [v one,v two]
    (by simpa only [freeValue,freeContextTerm] using captured)
  simpa only [payload_free_lookup, payload_option_type] using looked

private theorem bound_lookup_returns (caller : Subst) (state : State)
    (context : List TypeExpr) (index : Nat) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.natural index), boundValue context]) :
    PureReturns program caller state (a "gslt:rule:row-at" [one, two]) state
      (encoded (CettaWire.encodeOption typeTerm context[index]?)) := by
  have looked := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
    (context.map typeTerm) one two
    (by simpa only [boundValue, boundContextTerm, encodeList_map, Function.id_comp] using captured)
  simpa only [List.getElem?_map, payload_option_type] using looked

private theorem type_option_equal_returns (caller : Subst) (state : State)
    (actual : Option TypeExpr) (expected : TypeExpr) (one two : String)
    (left : applySubst caller (v one) = encoded (CettaWire.encodeOption typeTerm actual))
    (right : applySubst caller (v two) = encoded (CettaWire.encodeOption typeTerm (some expected))) :
    PureReturns program caller state (a "==" [v one,v two]) state
      (Effects.boolean (actual == some expected)) := by
  have checked := CettaWireAtom.equality_captured_returns program caller state
    (CettaWire.encodeOption typeTerm actual) (CettaWire.encodeOption typeTerm (some expected))
    one two left right
  have equality : decide (CettaWire.encodeOption typeTerm actual =
      CettaWire.encodeOption typeTerm (some expected)) = (actual == some expected) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, typeOption_injective.eq_iff]
    simp only [beq_iff_eq]
  simpa only [equality] using checked


private def extendEquation : SpaceSemantics.Equation :=
  (RuleExecutionProgram.premiseSource.program.equations.filter
    (fun equation => equation.head == "gslt:premise:type-extend-count"))[0]'(by decide +kernel)
private def extendEnvironment (domain : TypeExpr) (count : Nat) (bound : List TypeExpr) : Subst :=
  [("bound", boundValue bound), ("count", encoded (.natural count)), ("domain", typeValue domain)]
private def extendNext : Atom :=
  a "let*" [.expression
    [.expression [v "previous", a "-" [v "count", encoded (.natural 1)]],
      .expression [v "tail", a "gslt:premise:type-extend-count" [v "domain", v "previous", v "bound"]]],
    a "LCons" [v "domain", v "tail"]]
private theorem extend_shape : extendEquation.body =
    a "if" [a "==" [v "count", encoded (.natural 0)], v "bound", extendNext] := by decide +kernel

private theorem extend_call (caller : Subst) (state : State) (domain : TypeExpr)
    (count : Nat) (bound : List TypeExpr) (one two three answer : Atom)
    (captured : [one,three].map (applySubst caller) = [typeValue domain, boundValue bound])
    (countReturned : PureReturns program caller state two state (encoded (.natural count)))
    (returned : PureReturns program (extendEnvironment domain count bound) state extendEquation.body state answer) :
    PureReturns program caller state (a "gslt:premise:type-extend-count" [one,two,three]) state answer := by
  apply call_returns program caller state state "gslt:premise:type-extend-count" [one,two,three] answer
    (by decide +kernel) _ (by decide)
  apply raw_argument_answers program caller state state "gslt:premise:type-extend-count"
    one [two,three] [] 0 [answer] (by decide +kernel)
  apply evaluated_argument_returns program caller state state state (.function "gslt:premise:type-extend-count")
    two (encoded (.natural count)) answer [three] [applySubst caller one] 1
    (by decide +kernel) countReturned
  apply raw_argument_answers program caller state state "gslt:premise:type-extend-count"
    three [] [applySubst caller one,encoded (.natural count)] 2 [answer] (by decide +kernel)
  have first : applySubst caller one = typeValue domain := (List.cons.inj captured).1
  have third : applySubst caller three = boundValue bound := (List.cons.inj (List.cons.inj captured).2).1
  simpa only [List.map_nil, List.nil_append, List.append_nil, List.cons_append, first, third, Nat.reduceAdd] using
    authored_function_arguments_return program caller (extendEnvironment domain count bound) state state
      "gslt:premise:type-extend-count" [typeValue domain,encoded (.natural count),boundValue bound] 3
      extendEquation.body answer (by decide) (by decide) (by
        have clause := PureData.named_equation_clause program "gslt:premise:type-extend-count"
          extendEquation ["domain","count","bound"]
          [typeValue domain,encoded (.natural count),boundValue bound]
          (by rfl) (by decide +kernel) (by decide) rfl
        simpa [extendEnvironment] using clause) returned

private theorem extend_body_returns (state : State) (domain : TypeExpr)
    (count : Nat) (bound : List TypeExpr) :
    PureReturns program (extendEnvironment domain count bound) state extendEquation.body state
      (boundValue (List.replicate count domain ++ bound)) := by
  induction count with
  | zero =>
      let caller := extendEnvironment domain 0 bound
      rw [extend_shape]
      apply QuantifiedLocal.bool_if_returns caller state _ true
      · simpa [caller, extendEnvironment, Term.natural.injEq] using
          CettaWireAtom.equality_evaluated_returns program caller state (.natural 0) (.natural 0)
            (v "count") (encoded (.natural 0)) (by decide +kernel) (by decide +kernel)
            (by simpa [caller,extendEnvironment,applySubst,Subst.lookup] using variable_returns program caller state "count")
            (grounded_returns program caller state (.int 0))
      · simpa [caller,extendEnvironment,List.replicate_zero,applySubst,Subst.lookup] using
          variable_returns program caller state "bound"
  | succ count ih =>
      let caller := extendEnvironment domain (count+1) bound
      let previous := ("previous", encoded (.natural count)) :: caller
      let final := ("tail", boundValue (List.replicate count domain ++ bound)) :: previous
      rw [extend_shape]
      apply QuantifiedLocal.bool_if_returns caller state _ false
      · simpa [caller, extendEnvironment, Term.natural.injEq] using
          CettaWireAtom.equality_evaluated_returns program caller state (.natural (count+1)) (.natural 0)
            (v "count") (encoded (.natural 0)) (by decide +kernel) (by decide +kernel)
            (by simpa [caller,extendEnvironment,applySubst,Subst.lookup] using variable_returns program caller state "count")
            (grounded_returns program caller state (.int 0))
      · change PureReturns program caller state extendNext state _
        unfold extendNext
        apply PureData.let_bindings_return (pairs := [(v "previous", a "-" [v "count",encoded (.natural 1)]),
          (v "tail",a "gslt:premise:type-extend-count" [v "domain",v "previous",v "bound"])])
        · apply PureData.BindingsReturn.cons (value := encoded (.natural count)) (bound := previous)
          · apply native_binary_call_returns program caller state state state state "-"
              (v "count") (encoded (.natural 1)) (encoded (.natural (count+1))) (encoded (.natural 1))
              (encoded (.natural count)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
              _ (grounded_returns program caller state (.int 1)) _ (by decide)
            · simpa [caller,extendEnvironment,applySubst,Subst.lookup] using variable_returns program caller state "count"
            · change (Except.ok (state,[Atom.grounded (.int (((count+1 : Nat) : Int)-1))]) : Effects.Result) =
                Except.ok (state,[.grounded (.int (count : Int))])
              simp
          · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,previous,caller,extendEnvironment]
          · apply PureData.BindingsReturn.cons (value := boundValue (List.replicate count domain ++ bound)) (bound := final)
            · apply extend_call previous state domain count bound (v "domain") (v "previous") (v "bound") _
                (by simp [previous,caller,extendEnvironment,applySubst,Subst.lookup])
                (by simpa [previous,applySubst,Subst.lookup] using variable_returns program previous state "previous")
              exact ih
            · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,final,previous,caller,extendEnvironment]
            · exact .nil _ _
        · simpa [List.replicate_succ,List.cons_append,boundValue,boundContextTerm,encodeList,CettaWireAtom.encode,
            CettaWireAtom.encodeMany,final,previous,caller,extendEnvironment,applySubst,applySubst.applySubstList,Subst.lookup] using
            constructor_variables_return program final state "LCons" ["domain","tail"] (by decide +kernel) (by decide)

/-- Multi-binder extension is exactly the original replicated domain context. -/
theorem extend_count_returns (state : State) (domain : TypeExpr)
    (count : Nat) (bound : List TypeExpr) :
    PureReturns program [] state
      (a "gslt:premise:type-extend-count" [typeValue domain,encoded (.natural count),boundValue bound]) state
      (boundValue (List.replicate count domain ++ bound)) :=
  extend_call [] state domain count bound _ _ _ _ (by simp)
    (grounded_returns program [] state (.int count)) (extend_body_returns state domain count bound)

private theorem extend_count_variable_returns (caller : Subst) (state : State) (domain : TypeExpr)
    (count : Nat) (bound : List TypeExpr) (one two three : String)
    (captured : [v one,v two,v three].map (applySubst caller) =
      [typeValue domain,encoded (.natural count),boundValue bound]) :
    PureReturns program caller state (a "gslt:premise:type-extend-count" [v one,v two,v three]) state
      (boundValue (List.replicate count domain ++ bound)) := by
  have second : applySubst caller (v two) = encoded (.natural count) :=
    (List.cons.inj (List.cons.inj captured).2).1
  apply extend_call caller state domain count bound (v one) (v two) (v three) _ _
    (by simpa only [second] using variable_returns program caller state two)
    (extend_body_returns state domain count bound)
  have first := (List.cons.inj captured).1
  have third := (List.cons.inj (List.cons.inj (List.cons.inj captured).2).2).1
  simp only [List.map_cons,List.map_nil,first,third]

#print axioms extend_count_returns

private theorem bool_and_as_if (first second : Bool) :
    (first && second) = (if first then second else false) := by cases first <;> rfl

private theorem beq_as_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (first second : α) :
    decide (first = second) = (first == second) := by
  apply Bool.eq_iff_iff.mpr
  simp

private theorem boolean_branch_returns (caller : Subst) (state : State)
    (condition yes no : Atom) (tested yesValue noValue : Bool)
    (conditionReturned : PureReturns program caller state condition state (Effects.boolean tested))
    (yesReturned : PureReturns program caller state yes state (Effects.boolean yesValue))
    (noReturned : PureReturns program caller state no state (Effects.boolean noValue)) :
    PureReturns program caller state (a "if" [condition,yes,no]) state
      (Effects.boolean (if tested then yesValue else noValue)) := by
  apply QuantifiedLocal.bool_if_returns caller state condition tested yes no _ conditionReturned
  cases tested <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact noReturned
  · exact yesReturned

private def hasValues (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : List Atom :=
  [declarationsValue language.terms,freeValue free,boundValue bound,patternValue pattern,typeValue expected]
def query (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) : Atom :=
  a RawHelper.has.head (hasValues language free bound pattern expected)

private def argumentTypeBody : Atom :=
  a "if" [a "gslt:premise:type-has" [v "declarations",v "free",v "bound",v "argument",v "expected"],
    a "gslt:premise:type-arguments" [v "declarations",v "free",v "bound",v "arguments-rest",v "parameters-rest"],
    Effects.boolean false]
private def argumentRepresentationBody : Atom :=
  a "if" [a "gslt:premise:parameter-representation" [v "parameter",v "argument"],
    argumentTypeBody,Effects.boolean false]
private def argumentTypeCases : SpaceSemantics.Cases :=
  [(.symbol "None",Effects.boolean false),(a "Some" [v "expected"],argumentRepresentationBody)]
private def argumentConsBody : Atom :=
  a "case" [a "gslt:premise:parameter-type" [v "parameter"],
    .expression (argumentTypeCases.map fun row => .expression [row.1,row.2])]
private def argumentCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil",.symbol "LNil"],Effects.boolean true),
   (.expression [a "LCons" [v "argument",v "arguments-rest"],
      a "LCons" [v "parameter",v "parameters-rest"]],argumentConsBody),
   (v "bad",Effects.boolean false)]
private theorem arguments_shape : (rawEquation .arguments).body =
    a "case" [.expression [v "arguments",v "parameters"],
      .expression (argumentCases.map fun row => .expression [row.1,row.2])] := by decide +kernel

private def elementConsBody : Atom :=
  a "if" [a "gslt:premise:type-has" [v "declarations",v "free",v "bound",v "pattern",v "element"],
    a "gslt:premise:type-elements" [v "declarations",v "free",v "bound",v "rest",v "element"],
    Effects.boolean false]
private def elementCases : SpaceSemantics.Cases :=
  [(.symbol "LNil",Effects.boolean true),(a "LCons" [v "pattern",v "rest"],elementConsBody)]
private theorem elements_shape : (rawEquation .elements).body =
    a "case" [v "elements",.expression (elementCases.map fun row => .expression [row.1,row.2])] := by decide +kernel

private theorem elements_returns_of (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (elements : List Pattern) (elementType : TypeExpr) (state : State)
    (children : ∀ pattern ∈ elements, ∀ expected,
      PureReturns program [] state (query language free bound pattern expected) state
        (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected))) :
    PureReturns program [] state
      (a RawHelper.elements.head [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue elements,typeValue elementType]) state
      (Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements elementType)) := by
  induction elements with
  | nil =>
      let caller := rawEnvironment .elements [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue [],typeValue elementType]
      apply raw_closed .elements state [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue [],typeValue elementType] _ rfl
      rw [elements_shape]
      apply QuantifiedLocal.branch_returns caller caller state (v "elements") (.symbol "LNil") elementCases
        (Effects.boolean true)
      · simpa [caller,rawEnvironment,RawHelper.names,InferenceCettaWire.encodePatterns,CettaWireAtom.encode,applySubst,Subst.lookup] using variable_returns program caller state "elements"
      · simp [elementCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom]
      · exact grounded_returns program caller state (.bool true)
  | cons pattern elements ih =>
      let caller := rawEnvironment .elements [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue (pattern::elements),typeValue elementType]
      let selected := ("rest",patternsValue elements) :: ("pattern",patternValue pattern) :: caller
      apply raw_closed .elements state [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue (pattern::elements),typeValue elementType] _ rfl
      rw [elements_shape]
      apply QuantifiedLocal.branch_returns caller selected state (v "elements") (patternsValue (pattern::elements))
        elementCases elementConsBody
      · simpa [caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup] using variable_returns program caller state "elements"
      · simp [elementCases,InferenceCettaWire.encodePatterns,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
          caller,selected,rawEnvironment,RawHelper.names,Subst.lookup]
      · unfold elementConsBody
        have first := raw_capture .has selected state
          [v "declarations",v "free",v "bound",v "pattern",v "element"]
          (hasValues language free bound pattern elementType) _ rfl
          (by simp [hasValues,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
          (children pattern (by simp) elementType)
        have tail := raw_capture .elements selected state
          [v "declarations",v "free",v "bound",v "rest",v "element"]
          [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements,typeValue elementType] _ rfl
          (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
          (ih (fun other membership => children other (by simp [membership])))
        have branch := boolean_branch_returns selected state _ _ _
          (checkHasType language (FreeTypeContext.ofList free) bound pattern elementType)
          (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements elementType) false
          first tail (grounded_returns program selected state (.bool false))
        simpa only [checkElementsHaveType,bool_and_as_if,RawHelper.head,Effects.boolean] using branch

private theorem arguments_returns_of (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam) (state : State)
    (children : ∀ pattern ∈ arguments, ∀ expected,
      PureReturns program [] state (query language free bound pattern expected) state
        (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected))) :
    PureReturns program [] state
      (a RawHelper.arguments.head [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue arguments,parametersValue parameters]) state
      (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)) := by
  induction arguments generalizing parameters with
  | nil =>
      let caller := rawEnvironment .arguments [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue [],parametersValue parameters]
      apply raw_closed .arguments state [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue [],parametersValue parameters] _ rfl
      rw [arguments_shape]
      cases parameters with
      | nil =>
          apply QuantifiedLocal.branch_returns caller caller state _
            (.expression [.symbol "LNil",.symbol "LNil"]) argumentCases (Effects.boolean true)
          · simpa [caller,rawEnvironment,RawHelper.names,InferenceCettaWire.encodePatterns,CettaWireAtom.encode,applySubst,Subst.lookup] using
              PureData.variables_return program caller state ["arguments","parameters"]
          · simp [argumentCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom]
          · exact grounded_returns program caller state (.bool true)
      | cons parameter parameters =>
          let selected := ("bad",.expression [.symbol "LNil",parametersValue (parameter::parameters)]) :: caller
          apply QuantifiedLocal.branch_returns caller selected state _
            (.expression [.symbol "LNil",parametersValue (parameter::parameters)]) argumentCases (Effects.boolean false)
          · simpa [caller,rawEnvironment,RawHelper.names,InferenceCettaWire.encodePatterns,CettaWireAtom.encode,applySubst,Subst.lookup] using
              PureData.variables_return program caller state ["arguments","parameters"]
          · simp [argumentCases,parametersValue,encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              caller,selected,rawEnvironment,RawHelper.names,Subst.lookup]
          · exact grounded_returns program selected state (.bool false)
  | cons argument arguments ih =>
      let caller := rawEnvironment .arguments [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue (argument::arguments),parametersValue parameters]
      apply raw_closed .arguments state [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue (argument::arguments),parametersValue parameters] _ rfl
      rw [arguments_shape]
      cases parameters with
      | nil =>
          let selected := ("bad",.expression [patternsValue (argument::arguments),.symbol "LNil"]) :: caller
          apply QuantifiedLocal.branch_returns caller selected state _
            (.expression [patternsValue (argument::arguments),.symbol "LNil"]) argumentCases (Effects.boolean false)
          · simpa [caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup] using
              PureData.variables_return program caller state ["arguments","parameters"]
          · simp [argumentCases,InferenceCettaWire.encodePatterns,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              caller,selected,rawEnvironment,RawHelper.names,Subst.lookup]
          · exact grounded_returns program selected state (.bool false)
      | cons parameter parameters =>
          let selected := ("parameters-rest",parametersValue parameters) :: ("parameter",encoded (parameterTerm parameter)) ::
            ("arguments-rest",patternsValue arguments) :: ("argument",patternValue argument) :: caller
          apply QuantifiedLocal.branch_returns caller selected state _
            (.expression [patternsValue (argument::arguments),parametersValue (parameter::parameters)]) argumentCases argumentConsBody
          · simpa [caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup] using
              PureData.variables_return program caller state ["arguments","parameters"]
          · simp [argumentCases,InferenceCettaWire.encodePatterns,parametersValue,encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              caller,selected,rawEnvironment,RawHelper.names,Subst.lookup]
          · unfold argumentConsBody
            have annotation := TypedParameters.parameter_type_captured_returns selected state parameter (v "parameter")
              (by simp [selected,applySubst,Subst.lookup])
            cases found : parameterType? parameter with
            | none =>
                apply QuantifiedLocal.branch_returns selected selected state _ (.symbol "None") argumentTypeCases (Effects.boolean false)
                · simpa only [found,TypedParameters.typeResult,CettaWire.encodeOption,CettaWireAtom.encode] using annotation
                · simp [argumentTypeCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom]
                · simpa only [checkArgumentsHaveTypes,found,Effects.boolean] using grounded_returns program selected state (.bool false)
            | some expected =>
                let inner := ("expected",typeValue expected) :: selected
                apply QuantifiedLocal.branch_returns selected inner state _ (a "Some" [typeValue expected]) argumentTypeCases argumentRepresentationBody
                · simpa only [found,TypedParameters.typeResult,CettaWire.encodeOption,CettaWireAtom.encode,CettaWireAtom.encodeMany] using annotation
                · simp [argumentTypeCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
                    caller,selected,inner,rawEnvironment,RawHelper.names,Subst.lookup]
                · unfold argumentRepresentationBody
                  have representation := TypedParameters.parameter_representation_captured_returns inner state parameter argument
                    (v "parameter") (v "argument") (by simp [inner,selected,applySubst,Subst.lookup])
                  have first := raw_capture .has inner state
                    [v "declarations",v "free",v "bound",v "argument",v "expected"]
                    (hasValues language free bound argument expected) _ rfl
                    (by simp [hasValues,inner,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
                    (children argument (by simp) expected)
                  have tail := raw_capture .arguments inner state
                    [v "declarations",v "free",v "bound",v "arguments-rest",v "parameters-rest"]
                    [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue arguments,parametersValue parameters] _ rfl
                    (by simp [inner,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
                    (ih parameters (fun other membership => children other (by simp [membership])))
                  have typed := boolean_branch_returns inner state _ _ _
                    (checkHasType language (FreeTypeContext.ofList free) bound argument expected)
                    (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters) false
                    first tail (grounded_returns program inner state (.bool false))
                  have typed' : PureReturns program inner state argumentTypeBody state
                      (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound argument expected &&
                        checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)) := by
                    simpa only [argumentTypeBody,bool_and_as_if,RawHelper.head,Effects.boolean] using typed
                  have checked := boolean_branch_returns inner state _ _ _
                    (matchesParameterRepresentation? parameter argument)
                    (checkHasType language (FreeTypeContext.ofList free) bound argument expected &&
                      checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters) false
                    representation typed' (grounded_returns program inner state (.bool false))
                  simp only [checkArgumentsHaveTypes,found]
                  rw [Bool.and_assoc]
                  simpa only [bool_and_as_if,argumentRepresentationBody,RawHelper.head,Effects.boolean] using checked

private def constructorNext : Atom :=
  a "gslt:premise:type-constructors" [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"]
private def constructorArgumentsBody : Atom :=
  a "if" [a "gslt:premise:type-arguments" [v "declarations",v "free",v "bound",v "arguments",v "parameters"],
    Effects.boolean true,constructorNext]
private def constructorParameterCases : SpaceSemantics.Cases :=
  [(a "LCons" [a "TermSimple" [v "parameter",a "TCollection" [v "kind",v "element"]],.symbol "LNil"],constructorNext),
   (v "ordinary",constructorArgumentsBody)]
private def constructorParameterBody : Atom :=
  a "case" [v "parameters",.expression (constructorParameterCases.map fun row => .expression [row.1,row.2])]
private def constructorTypeBody (mode : CollectionRepresentation) : Atom :=
  a "let" [v "result",a "TBase" [v "category"],
    a "if" [a "==" [v "expected",v "result"],
      (match mode with | .bare => constructorParameterBody | .wrapped => constructorArgumentsBody),constructorNext]]
private def constructorConsBody (mode : CollectionRepresentation) : Atom :=
  a "if" [a "==" [v "actual",v "label"],constructorTypeBody mode,constructorNext]
private def constructorCases : SpaceSemantics.Cases :=
  [(.symbol "LNil",Effects.boolean false),
    (a "LCons" [a "GrammarTypingV1" [v "actual",v "category",v "parameters"],v "rest"],constructorConsBody .bare),
    (a "LCons" [a "GrammarTypingWrappedV1" [v "actual",v "category",v "parameters"],v "rest"],constructorConsBody .wrapped)]
private theorem constructors_shape : (rawEquation .constructors).body =
    a "case" [v "remaining",.expression (constructorCases.map fun row => .expression [row.1,row.2])] := by decide +kernel

private theorem constructor_parameters_return (caller : Subst) (state : State) (rule : GrammarRule)
    (mode : rule.collectionRepresentation = .bare) (argumentResult restResult : Bool)
    (stored : applySubst caller (v "parameters") = parametersValue rule.params)
    (parameterFresh : Subst.lookup caller "parameter" = none)
    (kindFresh : Subst.lookup caller "kind" = none)
    (elementFresh : Subst.lookup caller "element" = none)
    (ordinaryFresh : Subst.lookup caller "ordinary" = none)
    (argumentsReturned : PureReturns program caller state
      (a "gslt:premise:type-arguments" [v "declarations",v "free",v "bound",v "arguments",v "parameters"])
      state (Effects.boolean argumentResult))
    (restReturned : PureReturns program caller state constructorNext state (Effects.boolean restResult)) :
    PureReturns program caller state constructorParameterBody state
      (Effects.boolean (if usesBareCollection? rule then restResult else argumentResult || restResult)) := by
  simp only [Subst.lookup] at parameterFresh kindFresh elementFresh ordinaryFresh
  by_cases bare : usesBareCollection? rule = true
  · obtain ⟨parameter,kind,element,shape⟩ := (usesBareCollection?_eq_true_iff rule).mp bare
    have shape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
    let selected := ("element",typeValue element) :: ("kind",encoded (InferenceCettaWire.encodeCollectionType kind)) ::
      ("parameter",encoded (.string parameter)) :: caller
    unfold constructorParameterBody
    apply QuantifiedLocal.branch_returns caller selected state (v "parameters") (parametersValue rule.params)
      constructorParameterCases constructorNext
    · simpa only [stored] using variable_returns program caller state "parameters"
    · simp [constructorParameterCases,shape,parametersValue,parameterTerm,typeValue,typeTerm,encodeList,
        CettaWireAtom.encode,CettaWireAtom.encodeMany,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues,matchAtom,selected,Subst.lookup,
        parameterFresh,kindFresh,elementFresh]
    · -- The added case fields do not alter the captured call operands.
      apply PureData.raw_capture_returns program caller selected state state RawHelper.constructors.head
        [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"]
        [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"] _
        (by decide +kernel) _ (by decide) _
        (by simpa only [constructorNext,RawHelper.head,bare,ite_true] using restReturned)
      · intro index bounded
        exact raw_arguments .constructors index (by simpa [RawHelper.names] using bounded)
      · simp [selected,applySubst,Subst.lookup]
  · have notBare : usesBareCollection? rule = false := Bool.eq_false_iff.mpr bare
    let selected := ("ordinary",parametersValue rule.params) :: caller
    unfold constructorParameterBody
    apply QuantifiedLocal.branch_returns caller selected state (v "parameters") (parametersValue rule.params)
      constructorParameterCases constructorArgumentsBody
    · simpa only [stored] using variable_returns program caller state "parameters"
    · cases rule with
      | mk label category parameters syntaxPattern evalPolicy algebra representation =>
          change representation = .bare at mode
          cases parameters with
          | nil => simp [constructorParameterCases,parametersValue,encodeList,CettaWireAtom.encode,selected,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,ordinaryFresh]
          | cons parameter rest =>
              cases rest with
              | cons next tail => simp [constructorParameterCases,parametersValue,encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
                  selected,SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
                  Subst.lookup,ordinaryFresh]
              | nil =>
                  cases parameter with
                  | simple name type =>
                      cases type with
                      | collection kind element => simp [usesBareCollection?, GrammarRule.bareParams, mode] at notBare
                      | _ => simp [constructorParameterCases,parametersValue,parameterTerm,typeTerm,encodeList,
                          CettaWireAtom.encode,CettaWireAtom.encodeMany,selected,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
                          SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,ordinaryFresh]
                  | abstractionNamed binder name type => simp [constructorParameterCases,parametersValue,parameterTerm,encodeList,
                      CettaWireAtom.encode,CettaWireAtom.encodeMany,selected,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,ordinaryFresh]
                  | multiAbstractionNamed binders name type => simp [constructorParameterCases,parametersValue,parameterTerm,encodeList,
                      CettaWireAtom.encode,CettaWireAtom.encodeMany,selected,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,ordinaryFresh]
    · have arguments := PureData.raw_capture_returns program caller selected state state RawHelper.arguments.head
          [v "declarations",v "free",v "bound",v "arguments",v "parameters"]
          [v "declarations",v "free",v "bound",v "arguments",v "parameters"] _
          (by decide +kernel) (by intro index bounded; exact raw_arguments .arguments index (by simpa [RawHelper.names] using bounded))
          (by decide) (by simp [selected,applySubst,Subst.lookup]) argumentsReturned
      have rest := PureData.raw_capture_returns program caller selected state state RawHelper.constructors.head
          [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"]
          [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"] _
          (by decide +kernel) (by intro index bounded; exact raw_arguments .constructors index (by simpa [RawHelper.names] using bounded))
          (by decide) (by simp [selected,applySubst,Subst.lookup]) restReturned
      unfold constructorArgumentsBody
      have checked := boolean_branch_returns selected state _ _ _ argumentResult true restResult
        arguments (grounded_returns program selected state (.bool true)) rest
      cases argumentResult <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.true_or,notBare,constructorArgumentsBody,constructorNext,RawHelper.head,Effects.boolean] using checked

private theorem constructors_returns_of (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (label : String) (arguments : List Pattern) (expected : TypeExpr)
    (remaining : List GrammarRule) (state : State)
    (children : ∀ pattern ∈ arguments, ∀ expected,
      PureReturns program [] state (query language free bound pattern expected) state
        (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected))) :
    PureReturns program [] state
      (a RawHelper.constructors.head [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (.string label),patternsValue arguments,typeValue expected,declarationsValue remaining]) state
      (Effects.boolean (remaining.any fun rule => rule.label == label && expected == .base rule.category &&
        !usesBareCollection? rule && checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments rule.params)) := by
  induction remaining with
  | nil =>
      let caller := rawEnvironment .constructors [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (.string label),patternsValue arguments,typeValue expected,declarationsValue []]
      apply raw_closed .constructors state [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (.string label),patternsValue arguments,typeValue expected,declarationsValue []] _ rfl
      rw [constructors_shape]
      apply QuantifiedLocal.branch_returns caller caller state (v "remaining") (.symbol "LNil") constructorCases (Effects.boolean false)
      · simpa [caller,rawEnvironment,RawHelper.names,declarationsValue,declarationsTerm,encodeList,CettaWireAtom.encode,applySubst,Subst.lookup] using variable_returns program caller state "remaining"
      · simp [constructorCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom]
      · exact grounded_returns program caller state (.bool false)
  | cons rule remaining ih =>
      let caller := rawEnvironment .constructors [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (.string label),patternsValue arguments,typeValue expected,declarationsValue (rule::remaining)]
      let selected := ("rest",declarationsValue remaining) :: ("parameters",parametersValue rule.params) ::
        ("category",encoded (.string rule.category)) :: ("actual",encoded (.string rule.label)) :: caller
      let restResult := remaining.any fun rule => rule.label == label && expected == .base rule.category &&
        !usesBareCollection? rule && checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments rule.params
      have restReturned : PureReturns program selected state constructorNext state (Effects.boolean restResult) :=
        raw_capture .constructors selected state
          [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"]
          [declarationsValue language.terms,freeValue free,boundValue bound,encoded (.string label),patternsValue arguments,
            typeValue expected,declarationsValue remaining] _ rfl
          (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup]) ih
      apply raw_closed .constructors state [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (.string label),patternsValue arguments,typeValue expected,declarationsValue (rule::remaining)] _ rfl
      rw [constructors_shape]
      apply QuantifiedLocal.branch_returns caller selected state (v "remaining") (declarationsValue (rule::remaining)) constructorCases (constructorConsBody rule.collectionRepresentation)
      · simpa [caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup] using variable_returns program caller state "remaining"
      · cases mode : rule.collectionRepresentation <;> simp [mode,constructorCases,declarationsValue,declarationsTerm,typingDeclarationTerm,InferenceCettaWire.encodeList,parametersValue,encodeList,
          CettaWireAtom.encode,CettaWireAtom.encodeMany,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues,matchAtom,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup]
      · unfold constructorConsBody
        have labelChecked := CettaWireAtom.equality_captured_returns program selected state (.string rule.label) (.string label)
          "actual" "label" (by simp [selected,applySubst,Subst.lookup])
          (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
        have typedReturned : PureReturns program selected state (constructorTypeBody rule.collectionRepresentation) state
            (Effects.boolean (if expected == .base rule.category then
                if usesBareCollection? rule then restResult else
                  checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments rule.params || restResult
              else restResult)) := by
          let result := ("result",typeValue (.base rule.category)) :: selected
          unfold constructorTypeBody
          apply QuantifiedLocal.named_let_returns selected state "result" _ (typeValue (.base rule.category)) _ _
          · simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup]
          · simpa [typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,selected,applySubst,Subst.lookup] using
              constructor_variables_return program selected state "TBase" ["category"] (by decide +kernel) (by decide)
          · have compared := CettaWireAtom.equality_captured_returns program result state (typeTerm expected) (typeTerm (.base rule.category))
                "expected" "result" (by simp [result,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
                (by simp [result,applySubst,Subst.lookup])
            have compared' : PureReturns program result state (a "==" [v "expected",v "result"]) state
                (Effects.boolean (expected == .base rule.category)) := by
              simpa only [typeTerm_injective.eq_iff,beq_as_decide] using compared
            have more := raw_capture .constructors result state
              [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "rest"]
              [declarationsValue language.terms,freeValue free,boundValue bound,encoded (.string label),patternsValue arguments,
                typeValue expected,declarationsValue remaining] _ rfl
              (by simp [result,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup]) ih
            have argumentReturned := raw_capture .arguments result state
              [v "declarations",v "free",v "bound",v "arguments",v "parameters"]
              [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue arguments,parametersValue rule.params] _ rfl
              (by simp [result,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
              (arguments_returns_of language free bound arguments rule.params state children)
            apply boolean_branch_returns result state _ _ _ _ _ _ compared' ?_ more
            cases mode : rule.collectionRepresentation with
            | wrapped =>
              have checked := boolean_branch_returns result state _ _ _ _ true restResult
                argumentReturned (grounded_returns program result state (.bool true)) more
              cases checkedArguments : checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments rule.params <;>
                simpa [mode, constructorArgumentsBody, usesBareCollection?, GrammarRule.bareParams,
                  constructorNext, RawHelper.head, Effects.boolean, checkedArguments] using checked
            | bare =>
              exact constructor_parameters_return result state rule mode _ restResult
                (by simp [result,selected,applySubst,Subst.lookup])
                (by simp [result,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
                (by simp [result,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
                (by simp [result,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
                (by simp [result,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
                argumentReturned more
        have folded := boolean_branch_returns selected state _ _ _ (rule.label == label) _ restResult
          (by simpa only [Term.string.injEq,beq_as_decide] using labelChecked) typedReturned restReturned
        cases labelEquality : (rule.label == label) <;>
          cases typeEquality : (expected == TypeExpr.base rule.category) <;>
          cases bare : usesBareCollection? rule <;>
          simpa [List.any_cons,labelEquality,typeEquality,bare,restResult] using folded

private def collectionNext : Atom :=
  a "gslt:premise:type-collection-declarations" [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"]
private def collectionElementsBody : Atom :=
  a "if" [a "gslt:premise:type-elements" [v "declarations",v "free",v "bound",v "elements",v "element"],
    Effects.boolean true,collectionNext]
private def collectionKindBody : Atom :=
  a "if" [a "==" [v "actual",v "kind"],collectionElementsBody,collectionNext]
private def collectionCategoryBody : Atom :=
  a "if" [a "==" [v "category",v "sort"],collectionKindBody,collectionNext]
private def collectionParameterCases : SpaceSemantics.Cases :=
  [(.expression [a "LCons" [a "TermSimple" [v "parameter",a "TCollection" [v "actual",v "element"]],.symbol "LNil"],
        a "TBase" [v "sort"]],collectionCategoryBody),
   (v "ordinary",collectionNext)]
private def collectionParameterBody : Atom :=
  a "case" [.expression [v "parameters",v "expected"],
    .expression (collectionParameterCases.map fun row => .expression [row.1,row.2])]
private def collectionDeclarationCases : SpaceSemantics.Cases :=
  [(.symbol "LNil",Effects.boolean false),
   (a "LCons" [a "GrammarTypingV1" [v "label",v "category",v "parameters"],v "rest"],collectionParameterBody),
   (a "LCons" [a "GrammarTypingWrappedV1" [v "label",v "category",v "parameters"],v "rest"],collectionNext)]
private theorem collections_shape : (rawEquation .collections).body =
    a "case" [v "remaining",.expression (collectionDeclarationCases.map fun row => .expression [row.1,row.2])] := by decide +kernel

private theorem kindTerm_injective : Function.Injective InferenceCettaWire.encodeCollectionType := by
  intro first second same
  cases first <;> cases second <;> simp_all [InferenceCettaWire.encodeCollectionType]

private theorem collection_fallback_selected (caller : Subst) (parameters : List TermParam) (expected : TypeExpr)
    (ordinaryFresh : Subst.lookup caller "ordinary" = none)
    (unsupported : ¬ ∃ name actual element sort,
      parameters = [.simple name (.collection actual element)] ∧ expected = .base sort) :
    SpaceSemantics.selectCase caller (.expression [parametersValue parameters,typeValue expected]) collectionParameterCases =
      some (("ordinary",.expression [parametersValue parameters,typeValue expected]) :: caller,collectionNext) := by
  simp only [Subst.lookup] at ordinaryFresh
  cases expected <;> cases parameters with
  | nil => simp [collectionParameterCases,parametersValue,typeValue,encodeList,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
      Subst.lookup,ordinaryFresh]
  | cons parameter rest =>
      cases rest with
      | cons next tail => simp [collectionParameterCases,parametersValue,typeValue,encodeList,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
          Subst.lookup,ordinaryFresh]
      | nil =>
          cases parameter with
          | simple name type =>
              cases type <;>
                first
                | (exfalso; apply unsupported; exact ⟨_,_,_,_,rfl,rfl⟩)
                | simp [collectionParameterCases,parametersValue,typeValue,parameterTerm,encodeList,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
                    Subst.lookup,ordinaryFresh]
          | abstractionNamed binder name type => simp [collectionParameterCases,parametersValue,typeValue,parameterTerm,encodeList,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              Subst.lookup,ordinaryFresh]
          | multiAbstractionNamed binders name type => simp [collectionParameterCases,parametersValue,typeValue,parameterTerm,encodeList,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              Subst.lookup,ordinaryFresh]

private theorem collection_parameters_return (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (elements : List Pattern) (rule : GrammarRule) (kind : CollType) (expected : TypeExpr) (restResult : Bool)
    (mode : rule.collectionRepresentation = .bare)
    (stored : [v "parameters",v "expected"].map (applySubst caller) =
      [parametersValue rule.params,typeValue expected])
    (fields : [v "declarations",v "free",v "bound",v "elements"].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements])
    (kindStored : applySubst caller (v "kind") = encoded (InferenceCettaWire.encodeCollectionType kind))
    (categoryStored : applySubst caller (v "category") = encoded (.string rule.category))
    (parameterFresh : Subst.lookup caller "parameter" = none)
    (actualFresh : Subst.lookup caller "actual" = none)
    (elementFresh : Subst.lookup caller "element" = none)
    (sortFresh : Subst.lookup caller "sort" = none)
    (ordinaryFresh : Subst.lookup caller "ordinary" = none)
    (children : ∀ pattern ∈ elements, ∀ expected,
      PureReturns program [] state (query language free bound pattern expected) state
        (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)))
    (restReturned : PureReturns program caller state collectionNext state (Effects.boolean restResult)) :
    PureReturns program caller state collectionParameterBody state
      (Effects.boolean ((match bareCollectionElementType? rule kind expected with
        | none => false
        | some element => checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element) || restResult)) := by
  simp only [Subst.lookup] at parameterFresh actualFresh elementFresh sortFresh ordinaryFresh
  have parameterStored : applySubst caller (v "parameters") = parametersValue rule.params := (List.cons.inj stored).1
  have expectedStored : applySubst caller (v "expected") = typeValue expected := (List.cons.inj (List.cons.inj stored).2).1
  have values : PureReturns program caller state (.expression [v "parameters",v "expected"]) state
      (.expression [parametersValue rule.params,typeValue expected]) := by
    simpa only [List.map_cons,List.map_nil,parameterStored,expectedStored] using PureData.variables_return program caller state ["parameters","expected"]
  unfold collectionParameterBody
  by_cases supported : ∃ name actual element sort,
      rule.params = [.simple name (.collection actual element)] ∧ expected = .base sort
  · obtain ⟨name,actual,element,sort,shape,rfl⟩ := supported
    let selected := ("sort",encoded (.string sort)) :: ("element",typeValue element) ::
      ("actual",encoded (InferenceCettaWire.encodeCollectionType actual)) :: ("parameter",encoded (.string name)) :: caller
    apply QuantifiedLocal.branch_returns caller selected state _
      (.expression [parametersValue rule.params,typeValue (.base sort)]) collectionParameterCases collectionCategoryBody values
    · simp [collectionParameterCases,shape,parametersValue,typeValue,parameterTerm,typeTerm,encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
        selected,Subst.lookup,parameterFresh,actualFresh,elementFresh,sortFresh]
    · have passedFields : [v "declarations",v "free",v "bound",v "elements"].map (applySubst selected) =
          [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements] := by
        simpa [selected,applySubst,Subst.lookup] using fields
      have elementsReturned := raw_capture .elements selected state
        [v "declarations",v "free",v "bound",v "elements",v "element"]
        [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements,typeValue element] _ rfl
        (by simpa [selected,applySubst,Subst.lookup] using congrArg (fun xs => xs ++ [typeValue element]) passedFields)
        (elements_returns_of language free bound elements element state children)
      have more := PureData.raw_capture_returns program caller selected state state RawHelper.collections.head
        [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"]
        [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"] _
        (by decide +kernel) (by intro index bounded; exact raw_arguments .collections index (by simpa [RawHelper.names] using bounded))
        (by decide) (by simp [selected,applySubst,Subst.lookup]) restReturned
      have elementBranch := boolean_branch_returns selected state _ _ _
        (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element) true restResult
        elementsReturned (grounded_returns program selected state (.bool true)) more
      have elementBranch' : PureReturns program selected state collectionElementsBody state
          (Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element || restResult)) := by
        cases result : checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element <;>
          simpa only [collectionElementsBody,collectionNext,RawHelper.head,Effects.boolean,result,Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.true_or] using elementBranch
      have kindCompared := CettaWireAtom.equality_captured_returns program selected state
        (InferenceCettaWire.encodeCollectionType actual) (InferenceCettaWire.encodeCollectionType kind)
        "actual" "kind" (by simp [selected,applySubst,Subst.lookup])
        (by simpa [selected,applySubst,Subst.lookup] using kindStored)
      have kindBranch := boolean_branch_returns selected state _ _ _ (decide (actual=kind)) _ restResult
        (by simpa only [kindTerm_injective.eq_iff] using kindCompared) elementBranch' more
      have categoryCompared := CettaWireAtom.equality_captured_returns program selected state (.string rule.category) (.string sort)
        "category" "sort" (by simpa [selected,applySubst,Subst.lookup] using categoryStored)
        (by simp [selected,applySubst,Subst.lookup])
      have categoryBranch := boolean_branch_returns selected state _ _ _ (decide (rule.category=sort)) _ restResult
        (by simpa only [Term.string.injEq] using categoryCompared)
        (by simpa only [collectionKindBody] using kindBranch) more
      by_cases categorySame : rule.category=sort <;> by_cases kindSame : actual=kind <;>
        simpa [collectionCategoryBody,bareCollectionElementType?,GrammarRule.bareParams,mode,shape,categorySame,kindSame,collectionKindBody,collectionNext,RawHelper.head,Effects.boolean] using categoryBranch
  · let selected := ("ordinary",.expression [parametersValue rule.params,typeValue expected]) :: caller
    apply QuantifiedLocal.branch_returns caller selected state _
      (.expression [parametersValue rule.params,typeValue expected]) collectionParameterCases collectionNext values
      (collection_fallback_selected caller rule.params expected ordinaryFresh supported)
    have absent : bareCollectionElementType? rule kind expected = none := by
      cases found : bareCollectionElementType? rule kind expected with
      | none => rfl
      | some element =>
          obtain ⟨expectedShape,name,shape⟩ := (bareCollectionElementType?_eq_some_iff rule kind expected element).mp found
          exact False.elim (supported ⟨name,kind,element,rule.category,
            (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2,expectedShape⟩)
    apply PureData.raw_capture_returns program caller selected state state RawHelper.collections.head
      [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"]
      [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"] _
      (by decide +kernel) (by intro index bounded; exact raw_arguments .collections index (by simpa [RawHelper.names] using bounded))
      (by decide) (by simp [selected,applySubst,Subst.lookup])
      (by simpa only [absent,Bool.false_or,collectionNext,RawHelper.head] using restReturned)

private theorem collections_returns_of (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (kind : CollType) (elements : List Pattern) (expected : TypeExpr)
    (remaining : List GrammarRule) (state : State)
    (children : ∀ pattern ∈ elements, ∀ expected,
      PureReturns program [] state (query language free bound pattern expected) state
        (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected))) :
    PureReturns program [] state
      (a RawHelper.collections.head [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue remaining]) state
      (Effects.boolean (remaining.any fun rule => match bareCollectionElementType? rule kind expected with
        | none => false
        | some elementType => checkElementsHaveType language (FreeTypeContext.ofList free) bound elements elementType)) := by
  induction remaining with
  | nil =>
      let caller := rawEnvironment .collections [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue []]
      apply raw_closed .collections state [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue []] _ rfl
      rw [collections_shape]
      apply QuantifiedLocal.branch_returns caller caller state (v "remaining") (.symbol "LNil") collectionDeclarationCases (Effects.boolean false)
      · simpa [caller,rawEnvironment,RawHelper.names,declarationsValue,declarationsTerm,encodeList,CettaWireAtom.encode,applySubst,Subst.lookup] using variable_returns program caller state "remaining"
      · simp [collectionDeclarationCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom]
      · exact grounded_returns program caller state (.bool false)
  | cons rule remaining ih =>
      let caller := rawEnvironment .collections [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue (rule::remaining)]
      let selected := ("rest",declarationsValue remaining) :: ("parameters",parametersValue rule.params) ::
        ("category",encoded (.string rule.category)) :: ("label",encoded (.string rule.label)) :: caller
      let restResult := remaining.any fun rule => match bareCollectionElementType? rule kind expected with
        | none => false
        | some elementType => checkElementsHaveType language (FreeTypeContext.ofList free) bound elements elementType
      have restReturned : PureReturns program selected state collectionNext state (Effects.boolean restResult) :=
        raw_capture .collections selected state
          [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "rest"]
          [declarationsValue language.terms,freeValue free,boundValue bound,encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,
            typeValue expected,declarationsValue remaining] _ rfl
          (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup]) ih
      apply raw_closed .collections state [declarationsValue language.terms,freeValue free,boundValue bound,
        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue (rule::remaining)] _ rfl
      rw [collections_shape]
      apply QuantifiedLocal.branch_returns caller selected state (v "remaining") (declarationsValue (rule::remaining)) collectionDeclarationCases
        (match rule.collectionRepresentation with | .bare => collectionParameterBody | .wrapped => collectionNext)
      · simpa [caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup] using variable_returns program caller state "remaining"
      · cases mode : rule.collectionRepresentation <;> simp [mode,collectionDeclarationCases,declarationsValue,declarationsTerm,typingDeclarationTerm,InferenceCettaWire.encodeList,parametersValue,encodeList,
          CettaWireAtom.encode,CettaWireAtom.encodeMany,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues,matchAtom,selected,caller,rawEnvironment,RawHelper.names,Subst.lookup]
      · cases mode : rule.collectionRepresentation with
        | wrapped =>
          simpa [List.any_cons, bareCollectionElementType?, GrammarRule.bareParams, mode, restResult] using restReturned
        | bare =>
          simpa only [List.any_cons] using collection_parameters_return selected state language free bound elements rule kind expected restResult mode
            (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
            (by simp [selected,applySubst,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup])
            (by simp [selected,caller,rawEnvironment,RawHelper.names,Subst.lookup]) children restReturned

private def typeLookupBody (lookup : Atom) : Atom :=
  a "let*" [.expression [.expression [v "actual",lookup],
    .expression [v "wanted",a "Some" [v "expected"]]],a "==" [v "actual",v "wanted"]]
private def typeConstructorBody : Atom :=
  a RawHelper.constructors.head [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "declarations"]
private def typeLambdaInner : Atom :=
  a RawHelper.has.head [v "declarations",v "free",v "inner",v "body",v "codomain"]
private def typeLambdaBody : Atom :=
  a "let" [v "inner",a "LCons" [v "domain",v "bound"],typeLambdaInner]
private def typeMultiLambdaBody : Atom :=
  a "let" [v "inner",a "gslt:premise:type-extend-count" [v "domain",v "arity",v "bound"],typeLambdaInner]
private def typeLambdaCases : SpaceSemantics.Cases :=
  [(a "TArrow" [v "domain",v "codomain"],typeLambdaBody),(v "bad",Effects.boolean false)]
private def typeMultiLambdaCases : SpaceSemantics.Cases :=
  [(a "TArrow" [a "TMultiBinder" [v "domain"],v "codomain"],typeMultiLambdaBody),(v "bad",Effects.boolean false)]
private def typeCollectionDirectBody : Atom :=
  a "if" [a "==" [v "actual",v "kind"],
    a RawHelper.elements.head [v "declarations",v "free",v "bound",v "elements",v "element"],Effects.boolean false]
private def typeCollectionDeclarationBody : Atom :=
  a RawHelper.collections.head [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "declarations"]
private def typeCollectionCases : SpaceSemantics.Cases :=
  [(a "TCollection" [v "actual",v "element"],typeCollectionDirectBody),
   (v "base",typeCollectionDeclarationBody)]
private def typeCollectionRestCases : SpaceSemantics.Cases :=
  [(.symbol "RNone",a "case" [v "expected",.expression (typeCollectionCases.map fun row => .expression [row.1,row.2])]),
   (v "bad",Effects.boolean false)]
private def typeCases : SpaceSemantics.Cases :=
  [(a "Var" [v "index"],typeLookupBody (a "gslt:rule:row-at" [v "index",v "bound"])),
   (a "FVar" [v "name"],typeLookupBody (a "gslt:automata:binding" [v "name",v "free"])),
   (a "PApp" [v "label",v "arguments"],typeConstructorBody),
   (a "PLam" [v "binder",v "body"],a "case" [v "expected",.expression (typeLambdaCases.map fun row => .expression [row.1,row.2])]),
   (a "PMultiLam" [v "arity",v "binders",v "body"],a "case" [v "expected",.expression (typeMultiLambdaCases.map fun row => .expression [row.1,row.2])]),
   (a "PSubst" [v "body",v "replacement"],Effects.boolean false),
   (a "PCollection" [v "kind",v "elements",v "rest"],a "case" [v "rest",.expression (typeCollectionRestCases.map fun row => .expression [row.1,row.2])]),
   (v "bad",Effects.boolean false)]
private theorem type_has_shape : (rawEquation .has).body =
  a "case" [v "pattern",.expression (typeCases.map fun row => .expression [row.1,row.2])] := by decide +kernel

private theorem type_lookup_returns (caller : Subst) (state : State) (lookup : Atom)
    (actual : Option TypeExpr) (expected : TypeExpr)
    (stored : applySubst caller (v "expected") = typeValue expected)
    (actualFresh : Subst.lookup caller "actual" = none)
    (wantedFresh : Subst.lookup caller "wanted" = none)
    (looked : PureReturns program caller state lookup state
      (encoded (CettaWire.encodeOption typeTerm actual))) :
    PureReturns program caller state (typeLookupBody lookup) state (Effects.boolean (actual == some expected)) := by
  simp only [Subst.lookup] at actualFresh wantedFresh
  let afterLookup := ("actual",encoded (CettaWire.encodeOption typeTerm actual)) :: caller
  let afterWanted := ("wanted",encoded (CettaWire.encodeOption typeTerm (some expected))) :: afterLookup
  have expectedCaptured : applySubst afterLookup (v "expected") = typeValue expected := by
    simpa [afterLookup,applySubst,Subst.lookup] using stored
  unfold typeLookupBody
  apply PureData.let_bindings_return (pairs := [(v "actual",lookup),(v "wanted",a "Some" [v "expected"])])
  · apply PureData.BindingsReturn.cons (value := encoded (CettaWire.encodeOption typeTerm actual)) (bound := afterLookup) looked
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,actualFresh,afterLookup]
    · apply PureData.BindingsReturn.cons (value := encoded (CettaWire.encodeOption typeTerm (some expected))) (bound := afterWanted)
      · simpa only [CettaWire.encodeOption,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          List.map_cons,List.map_nil,expectedCaptured] using
          constructor_variables_return program afterLookup state "Some" ["expected"] (by decide +kernel) (by decide)
      · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,wantedFresh,afterWanted,afterLookup]
      · exact .nil _ _
  · exact type_option_equal_returns afterWanted state actual expected "actual" "wanted"
      (by simp [afterWanted,afterLookup,applySubst,Subst.lookup]) (by simp [afterWanted,applySubst,Subst.lookup])

private theorem lambda_fallback_selected (caller : Subst) (expected : TypeExpr)
    (fresh : Subst.lookup caller "bad" = none)
    (unsupported : ¬ ∃ domain codomain, expected = .arrow domain codomain) :
    SpaceSemantics.selectCase caller (typeValue expected) typeLambdaCases =
      some (("bad",typeValue expected) :: caller,Effects.boolean false) := by
  simp only [Subst.lookup] at fresh
  cases expected with
  | arrow domain codomain => exact False.elim (unsupported ⟨domain,codomain,rfl⟩)
  | _ => simp [typeLambdaCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,fresh]

private theorem multi_lambda_fallback_selected (caller : Subst) (expected : TypeExpr)
    (fresh : Subst.lookup caller "bad" = none)
    (unsupported : ¬ ∃ domain codomain, expected = .arrow (.multiBinder domain) codomain) :
    SpaceSemantics.selectCase caller (typeValue expected) typeMultiLambdaCases =
      some (("bad",typeValue expected) :: caller,Effects.boolean false) := by
  simp only [Subst.lookup] at fresh
  cases expected with
  | arrow domain codomain =>
      cases domain with
      | multiBinder domain => exact False.elim (unsupported ⟨domain,codomain,rfl⟩)
      | _ => simp [typeMultiLambdaCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,fresh]
  | _ => simp [typeMultiLambdaCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,fresh]

private theorem collection_type_fallback_selected (caller : Subst) (expected : TypeExpr)
    (fresh : Subst.lookup caller "base" = none)
    (unsupported : ¬ ∃ kind element, expected = .collection kind element) :
    SpaceSemantics.selectCase caller (typeValue expected) typeCollectionCases =
      some (("base",typeValue expected) :: caller,typeCollectionDeclarationBody) := by
  simp only [Subst.lookup] at fresh
  cases expected with
  | collection kind element => exact False.elim (unsupported ⟨kind,element,rfl⟩)
  | _ => simp [typeCollectionCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
      SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,fresh]

private theorem has_branch_returns (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) (state : State)
    (selected : Subst) (body : Atom)
    (selectedCase : SpaceSemantics.selectCase (rawEnvironment .has (hasValues language free bound pattern expected))
      (patternValue pattern) typeCases = some (selected,body))
    (returned : PureReturns program selected state body state
      (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected))) :
    PureReturns program [] state (query language free bound pattern expected) state
      (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)) := by
  let caller := rawEnvironment .has (hasValues language free bound pattern expected)
  apply raw_closed .has state (hasValues language free bound pattern expected) _ rfl
  rw [type_has_shape]
  apply QuantifiedLocal.branch_returns caller selected state (v "pattern") (patternValue pattern) typeCases body
  · simpa [caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program caller state "pattern"
  · exact selectedCase
  · exact returned

/-- The actual retained typing program agrees on every original pattern.
Every child call is derived by the original syntax induction, including
ambient contexts extended by single and multiple binders. -/
theorem check_has_type_returns (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) (state : State) :
    PureReturns program [] state (query language free bound pattern expected) state
      (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)) := by
  induction pattern using Pattern.inductionOn generalizing bound expected with
  | hbvar index =>
      let caller := rawEnvironment .has (hasValues language free bound (.bvar index) expected)
      let selected := ("index",encoded (.natural index)) :: caller
      apply has_branch_returns language free bound (.bvar index) expected state selected
        (typeLookupBody (a "gslt:rule:row-at" [v "index",v "bound"]))
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · simpa only [checkHasType] using type_lookup_returns selected state
          (a "gslt:rule:row-at" [v "index",v "bound"]) bound[index]? expected
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup])
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup])
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup])
          (bound_lookup_returns selected state bound index (v "index") (v "bound")
            (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup]))
  | hfvar name =>
      let caller := rawEnvironment .has (hasValues language free bound (.fvar name) expected)
      let selected := ("name",encoded (.string name)) :: caller
      apply has_branch_returns language free bound (.fvar name) expected state selected
        (typeLookupBody (a "gslt:automata:binding" [v "name",v "free"]))
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · simpa only [checkHasType] using type_lookup_returns selected state
          (a "gslt:automata:binding" [v "name",v "free"]) (FreeTypeContext.ofList free name) expected
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup])
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup])
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup])
          (free_lookup_returns selected state free name "name" "free"
            (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup]))
  | happly label arguments ih =>
      let caller := rawEnvironment .has (hasValues language free bound (.apply label arguments) expected)
      let selected := ("arguments",patternsValue arguments) :: ("label",encoded (.string label)) :: caller
      apply has_branch_returns language free bound (.apply label arguments) expected state selected typeConstructorBody
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · exact raw_capture .constructors selected state
          [v "declarations",v "free",v "bound",v "label",v "arguments",v "expected",v "declarations"]
          [declarationsValue language.terms,freeValue free,boundValue bound,encoded (.string label),patternsValue arguments,
            typeValue expected,declarationsValue language.terms] _ rfl
          (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup])
          (constructors_returns_of language free bound label arguments expected language.terms state
            (fun child member childExpected => ih child member bound childExpected))
  | hlambda binder body ih =>
      let caller := rawEnvironment .has (hasValues language free bound (.lambda binder body) expected)
      let selected := ("body",patternValue body) :: ("binder",encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      apply has_branch_returns language free bound (.lambda binder body) expected state selected
        (a "case" [v "expected",.expression (typeLambdaCases.map fun row => .expression [row.1,row.2])])
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · by_cases supported : ∃ domain codomain, expected = .arrow domain codomain
        · obtain ⟨domain,codomain,rfl⟩ := supported
          let entered := ("codomain",typeValue codomain) :: ("domain",typeValue domain) :: selected
          apply QuantifiedLocal.branch_returns selected entered state (v "expected") (typeValue (.arrow domain codomain))
            typeLambdaCases typeLambdaBody
          · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
          · simp [typeLambdaCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
          · let inner := ("inner",boundValue (domain::bound)) :: entered
            unfold typeLambdaBody
            apply QuantifiedLocal.named_let_returns entered state "inner" _ (boundValue (domain::bound)) typeLambdaInner _
            · simp [entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
            · simpa [boundValue,boundContextTerm,encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
                entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using
                constructor_variables_return program entered state "LCons" ["domain","bound"] (by decide +kernel) (by decide)
            · exact raw_capture .has inner state [v "declarations",v "free",v "inner",v "body",v "codomain"]
                (hasValues language free (domain::bound) body codomain) _ rfl
                (by simp [hasValues,inner,entered,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
                (ih (domain::bound) codomain)
        · let rejected := ("bad",typeValue expected) :: selected
          have refused : checkHasType language (FreeTypeContext.ofList free) bound (.lambda binder body) expected = false := by
            cases expected with
            | arrow domain codomain => exact False.elim (supported ⟨domain,codomain,rfl⟩)
            | _ => rfl
          rw [refused]
          apply QuantifiedLocal.branch_returns selected rejected state (v "expected") (typeValue expected) typeLambdaCases (Effects.boolean false)
          · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
          · exact lambda_fallback_selected selected expected (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]) supported
          · exact grounded_returns program rejected state (.bool false)
  | hmultiLambda arity binders body ih =>
      let caller := rawEnvironment .has (hasValues language free bound (.multiLambda arity binders body) expected)
      let selected := ("body",patternValue body) :: ("binders",encoded (encodeList Term.string binders)) ::
        ("arity",encoded (.natural arity)) :: caller
      apply has_branch_returns language free bound (.multiLambda arity binders body) expected state selected
        (a "case" [v "expected",.expression (typeMultiLambdaCases.map fun row => .expression [row.1,row.2])])
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,InferenceCettaWire.encodeList,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · by_cases supported : ∃ domain codomain, expected = .arrow (.multiBinder domain) codomain
        · obtain ⟨domain,codomain,rfl⟩ := supported
          let entered := ("codomain",typeValue codomain) :: ("domain",typeValue domain) :: selected
          apply QuantifiedLocal.branch_returns selected entered state (v "expected") (typeValue (.arrow (.multiBinder domain) codomain))
            typeMultiLambdaCases typeMultiLambdaBody
          · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
          · simp [typeMultiLambdaCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
              entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
          · let inner := ("inner",boundValue (List.replicate arity domain ++ bound)) :: entered
            unfold typeMultiLambdaBody
            apply QuantifiedLocal.named_let_returns entered state "inner" _ (boundValue (List.replicate arity domain ++ bound)) typeLambdaInner _
            · simp [entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
            · exact extend_count_variable_returns entered state domain arity bound "domain" "arity" "bound"
                (by simp [entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup])
            · exact raw_capture .has inner state [v "declarations",v "free",v "inner",v "body",v "codomain"]
                (hasValues language free (List.replicate arity domain ++ bound) body codomain) _ rfl
                (by simp [hasValues,inner,entered,selected,caller,rawEnvironment,RawHelper.names,applySubst,Subst.lookup])
                (ih (List.replicate arity domain ++ bound) codomain)
        · let rejected := ("bad",typeValue expected) :: selected
          have refused : checkHasType language (FreeTypeContext.ofList free) bound (.multiLambda arity binders body) expected = false := by
            cases expected with
            | arrow domain codomain =>
                cases domain with
                | multiBinder domain => exact False.elim (supported ⟨domain,codomain,rfl⟩)
                | _ => rfl
            | _ => rfl
          rw [refused]
          apply QuantifiedLocal.branch_returns selected rejected state (v "expected") (typeValue expected) typeMultiLambdaCases (Effects.boolean false)
          · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
          · exact multi_lambda_fallback_selected selected expected (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]) supported
          · exact grounded_returns program rejected state (.bool false)
  | hsubst body replacement _ _ =>
      let caller := rawEnvironment .has (hasValues language free bound (.subst body replacement) expected)
      let selected := ("replacement",patternValue replacement) :: ("body",patternValue body) :: caller
      apply has_branch_returns language free bound (.subst body replacement) expected state selected (Effects.boolean false)
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · exact grounded_returns program selected state (.bool false)
  | hcollection kind elements rest ih =>
      let caller := rawEnvironment .has (hasValues language free bound (.collection kind elements rest) expected)
      let selected := ("rest",encoded (InferenceCettaWire.encodeRest rest)) :: ("elements",patternsValue elements) ::
        ("kind",encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      apply has_branch_returns language free bound (.collection kind elements rest) expected state selected
        (a "case" [v "rest",.expression (typeCollectionRestCases.map fun row => .expression [row.1,row.2])])
      · simp [typeCases,hasValues,caller,selected,rawEnvironment,RawHelper.names,patternValue,
          InferenceCettaWire.encodePattern,CettaWireAtom.encode,CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]
      · cases rest with
        | some name =>
            let rejected := ("bad",encoded (InferenceCettaWire.encodeRest (some name))) :: selected
            apply QuantifiedLocal.branch_returns selected rejected state (v "rest") (encoded (InferenceCettaWire.encodeRest (some name))) typeCollectionRestCases (Effects.boolean false)
            · simpa [selected,applySubst,Subst.lookup] using variable_returns program selected state "rest"
            · simp [typeCollectionRestCases,InferenceCettaWire.encodeRest,CettaWireAtom.encode,CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,rejected,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
            · exact grounded_returns program rejected state (.bool false)
        | none =>
            apply QuantifiedLocal.branch_returns selected selected state (v "rest") (.symbol "RNone") typeCollectionRestCases
              (a "case" [v "expected",.expression (typeCollectionCases.map fun row => .expression [row.1,row.2])])
            · simpa [selected,InferenceCettaWire.encodeRest,CettaWireAtom.encode,applySubst,Subst.lookup] using variable_returns program selected state "rest"
            · simp [typeCollectionRestCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom]
            · by_cases supported : ∃ actual element, expected = .collection actual element
              · obtain ⟨actual,element,rfl⟩ := supported
                let entered := ("element",typeValue element) :: ("actual",encoded (InferenceCettaWire.encodeCollectionType actual)) :: selected
                apply QuantifiedLocal.branch_returns selected entered state (v "expected") (typeValue (.collection actual element))
                  typeCollectionCases typeCollectionDirectBody
                · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
                · simp [typeCollectionCases,typeValue,typeTerm,CettaWireAtom.encode,CettaWireAtom.encodeMany,
                    SpaceSemantics.selectCase,SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,
                    entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]
                · have compared := CettaWireAtom.equality_captured_returns program entered state
                    (InferenceCettaWire.encodeCollectionType actual) (InferenceCettaWire.encodeCollectionType kind) "actual" "kind"
                    (by simp [entered,applySubst,Subst.lookup]) (by simp [entered,selected,applySubst,Subst.lookup])
                  have children := elements_returns_of language free bound elements element state
                    (fun child member childExpected => ih child member bound childExpected)
                  have returned := raw_capture .elements entered state [v "declarations",v "free",v "bound",v "elements",v "element"]
                    [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements,typeValue element] _ rfl
                    (by simp [entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup]) children
                  have branch := boolean_branch_returns entered state _ _ _ (actual==kind)
                    (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element) false
                    (by simpa only [kindTerm_injective.eq_iff,beq_as_decide] using compared) returned
                    (grounded_returns program entered state (.bool false))
                  have absent : ∀ rule : GrammarRule, bareCollectionElementType? rule kind (.collection actual element) = none := by
                    intro rule; simp [bareCollectionElementType?]
                  have canonical : checkHasType language (FreeTypeContext.ofList free) bound
                      (.collection kind elements none) (.collection actual element) =
                      (actual == kind && checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element) := by
                    simp only [checkHasType,Option.isNone_none,Bool.true_and,absent]
                    rw [show language.terms.any (fun _ : GrammarRule => false) = false from
                      List.any_eq_false.mpr (by intro rule member; simp), Bool.or_false]
                  simpa only [canonical,bool_and_as_if,typeCollectionDirectBody,RawHelper.head,
                    a,v,Effects.boolean] using branch
              ·
                  let entered := ("base",typeValue expected) :: selected
                  apply QuantifiedLocal.branch_returns selected entered state (v "expected") (typeValue expected) typeCollectionCases typeCollectionDeclarationBody
                  · simpa [selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup] using variable_returns program selected state "expected"
                  · exact collection_type_fallback_selected selected expected
                      (by simp [selected,caller,rawEnvironment,RawHelper.names,hasValues,Subst.lookup]) supported
                  · have returned := raw_capture .collections entered state
                      [v "declarations",v "free",v "bound",v "kind",v "elements",v "expected",v "declarations"]
                      [declarationsValue language.terms,freeValue free,boundValue bound,
                        encoded (InferenceCettaWire.encodeCollectionType kind),patternsValue elements,typeValue expected,declarationsValue language.terms] _ rfl
                      (by simp [entered,selected,caller,rawEnvironment,RawHelper.names,hasValues,applySubst,Subst.lookup])
                      (collections_returns_of language free bound kind elements expected language.terms state
                        (fun child member childExpected => ih child member bound childExpected))
                    have canonical : checkHasType language (FreeTypeContext.ofList free) bound (.collection kind elements none) expected =
                        language.terms.any (fun rule => match bareCollectionElementType? rule kind expected with
                          | none => false
                          | some element => checkElementsHaveType language (FreeTypeContext.ofList free) bound elements element) := by
                      cases expected with
                      | collection actual element => exact False.elim (supported ⟨actual,element,rfl⟩)
                      | _ =>
                          simp only [checkHasType,Option.isNone_none,Bool.true_and,Bool.false_or]
                          all_goals
                            congr 1 <;> funext rule <;> split <;> rename_i equation <;> simp only [equation]
                    simpa only [canonical,typeCollectionDeclarationBody,RawHelper.head] using returned

/-- Ordered argument checking uses the same whole-pattern theorem for every
argument; no child-check contract is assumed at this boundary. -/
theorem check_arguments_have_types_returns (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam) (state : State) :
    PureReturns program [] state
      (a "gslt:premise:type-arguments" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue arguments,parametersValue parameters]) state
      (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)) :=
  arguments_returns_of language free bound arguments parameters state
    (fun pattern _ expected => check_has_type_returns language free bound pattern expected state)

theorem check_elements_have_type_returns (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr) (state : State) :
    PureReturns program [] state
      (a "gslt:premise:type-elements" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue elements,typeValue expected]) state
      (Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements expected)) :=
  elements_returns_of language free bound elements expected state
    (fun pattern _ expected => check_has_type_returns language free bound pattern expected state)

theorem check_has_type_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (pattern : Pattern) (expected : TypeExpr) (one two three four five : Atom)
    (captured : [one,two,three,four,five].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternValue pattern,typeValue expected]) :
    PureReturns program caller state (a "gslt:premise:type-has" [one,two,three,four,five]) state
      (Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)) :=
  raw_capture .has caller state [one,two,three,four,five] (hasValues language free bound pattern expected)
    _ rfl captured (check_has_type_returns language free bound pattern expected state)

theorem check_arguments_have_types_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (arguments : List Pattern) (parameters : List TermParam) (one two three four five : Atom)
    (captured : [one,two,three,four,five].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue arguments,parametersValue parameters]) :
    PureReturns program caller state (a "gslt:premise:type-arguments" [one,two,three,four,five]) state
      (Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)) :=
  raw_capture .arguments caller state [one,two,three,four,five]
    [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue arguments,parametersValue parameters]
    _ rfl captured (check_arguments_have_types_returns language free bound arguments parameters state)

theorem check_elements_have_type_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (elements : List Pattern) (expected : TypeExpr) (one two three four five : Atom)
    (captured : [one,two,three,four,five].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements,typeValue expected]) :
    PureReturns program caller state (a "gslt:premise:type-elements" [one,two,three,four,five]) state
      (Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements expected)) :=
  raw_capture .elements caller state [one,two,three,four,five]
    [declarationsValue language.terms,freeValue free,boundValue bound,patternsValue elements,typeValue expected]
    _ rfl captured (check_elements_have_type_returns language free bound elements expected state)

/-- Completed execution exposes the exact original Boolean and unchanged
state and I/O. A refusal is therefore an actual completed False result. -/
theorem check_has_type_completed_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state,control := .evaluate [] (query language free bound pattern expected)} =
      .complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (check_has_type_returns language free bound pattern expected state) after answers input output

theorem check_has_type_derivation_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language free bound pattern expected)}
      (.complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (check_has_type_returns language free bound pattern expected state) after answers input output

/-- The semantic typing conclusion is earned from the actual completed run. -/
theorem accepted_has_type {language : LanguageDef} {free : List (String × TypeExpr)}
    {bound : List TypeExpr} {pattern : Pattern} {expected : TypeExpr} {state : State}
    (accepted : DeclarativeSpec.Runs program {state,control := .evaluate [] (query language free bound pattern expected)}
      (.complete state [Effects.boolean true] [] [])) :
    HasType language (FreeTypeContext.ofList free) bound pattern expected := by
  have result := (check_has_type_derivation_iff language free bound pattern expected state state _ [] []).mp accepted
  have checked : checkHasType language (FreeTypeContext.ofList free) bound pattern expected = true := by
    simpa only [Effects.boolean,Atom.grounded.injEq,OSLFCore.GroundedValue.bool.injEq] using
      ((List.cons.inj result.2.1).1).symm
  exact checkHasType_sound checked

/-- Completeness is the original checker's object-pattern completeness, with
no widening to its schema-only substitution and collection-rest constructors. -/
theorem accepted_iff_has_type (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr) (state : State)
    (object : isObjectPattern pattern = true) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language free bound pattern expected)}
      (.complete state [Effects.boolean true] [] []) ↔
    HasType language (FreeTypeContext.ofList free) bound pattern expected := by
  constructor
  · exact accepted_has_type
  · intro typed
    have checked := checkHasType_complete_of_object typed object
    exact (check_has_type_derivation_iff language free bound pattern expected state state _ [] []).mpr
      ⟨rfl,by simp only [checked],rfl,rfl⟩

#print axioms check_has_type_returns
#print axioms check_arguments_have_types_returns
#print axioms check_elements_have_type_returns
#print axioms check_has_type_captured_returns
#print axioms check_arguments_have_types_captured_returns
#print axioms check_elements_have_type_captured_returns
#print axioms check_has_type_completed_iff
#print axioms check_has_type_derivation_iff
#print axioms accepted_has_type
#print axioms accepted_iff_has_type

/-- Captured execution keeps its caller environment distinct from the helper's
fresh parameter frame, while exposing the same state and I/O observation. -/
theorem check_has_type_captured_derivation_iff (caller : Subst) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (one two three four five : Atom)
    (captured : [one,two,three,four,five].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternValue pattern,typeValue expected])
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state,control := .evaluate caller (a "gslt:premise:type-has" [one,two,three,four,five])}
      (.complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program caller state state _ _
    (check_has_type_captured_returns caller state language free bound pattern expected one two three four five captured)
    after answers input output

theorem check_arguments_have_types_completed_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state,control := .evaluate [] (a "gslt:premise:type-arguments" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue arguments,parametersValue parameters])} = .complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (check_arguments_have_types_returns language free bound arguments parameters state) after answers input output

theorem check_arguments_have_types_derivation_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (a "gslt:premise:type-arguments" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue arguments,parametersValue parameters])} (.complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkArgumentsHaveTypes language (FreeTypeContext.ofList free) bound arguments parameters)] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (check_arguments_have_types_returns language free bound arguments parameters state) after answers input output

theorem check_elements_have_type_completed_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state,control := .evaluate [] (a "gslt:premise:type-elements" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue elements,typeValue expected])} = .complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (check_elements_have_type_returns language free bound elements expected state) after answers input output

theorem check_elements_have_type_derivation_iff (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (state after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (a "gslt:premise:type-elements" [declarationsValue language.terms,freeValue free,boundValue bound,
        patternsValue elements,typeValue expected])} (.complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkElementsHaveType language (FreeTypeContext.ofList free) bound elements expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (check_elements_have_type_returns language free bound elements expected state) after answers input output

#print axioms check_has_type_captured_derivation_iff
#print axioms check_arguments_have_types_completed_iff
#print axioms check_arguments_have_types_derivation_iff
#print axioms check_elements_have_type_completed_iff
#print axioms check_elements_have_type_derivation_iff

/-- Captured calls complete with the exact original Boolean and untouched I/O. -/
theorem check_has_type_captured_completed_iff (caller : Subst) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (one two three four five : Atom)
    (captured : [one,two,three,four,five].map (applySubst caller) =
      [declarationsValue language.terms,freeValue free,boundValue bound,patternValue pattern,typeValue expected])
    (state after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state,control := .evaluate caller (a "gslt:premise:type-has" [one,two,three,four,five])} =
      .complete after answers input output) ↔
    after = state ∧ answers = [Effects.boolean (checkHasType language (FreeTypeContext.ofList free) bound pattern expected)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff program caller state state _ _
    (check_has_type_captured_returns caller state language free bound pattern expected one two three four five captured)
    after answers input output

#print axioms check_has_type_captured_completed_iff

namespace SourceControls

private def expr : TypeExpr := .base "Expr"
private def nameType : TypeExpr := .base "Name"
private def declaration (label category : String) (params : List TermParam) : GrammarRule :=
  {label,category,params,syntaxPattern := []}
private def language : LanguageDef :=
  {name := "DeclarationTypingControls",types := ["Expr","Name","Expressions"],
   terms := [declaration "zero" "Expr" [],declaration "overload" "Name" [],
     declaration "overload" "Expr" [],
     declaration "vector" "Expressions" [.simple "items" (.collection .vec expr)],
     declaration "binding" "Expr" [.abstractionNamed (some "display") "body" (.arrow nameType expr)]],
   equations := [],rewrites := []}

/-- A wrong earlier overload must not suppress a correctly sorted later one. -/
theorem later_declaration_is_checked (state : State) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.apply "overload" []) expr)}
      (.complete state [Effects.boolean true] [] []) :=
  (check_has_type_derivation_iff language [] [] (.apply "overload" []) expr state state _ [] []).mpr
    ⟨rfl,by decide +kernel,rfl,rfl⟩

/-- The first free-variable declaration shadows later declarations. -/
theorem free_context_first_shadow (state : State) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [("x",nameType),("x",expr)] [] (.fvar "x") nameType)}
      (.complete state [Effects.boolean true] [] []) ∧
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [("x",nameType),("x",expr)] [] (.fvar "x") expr)}
      (.complete state [Effects.boolean false] [] []) :=
  ⟨(check_has_type_derivation_iff language [("x",nameType),("x",expr)] [] (.fvar "x") nameType state state _ [] []).mpr
    ⟨rfl,by decide +kernel,rfl,rfl⟩,
   (check_has_type_derivation_iff language [("x",nameType),("x",expr)] [] (.fvar "x") expr state state _ [] []).mpr
    ⟨rfl,by decide +kernel,rfl,rfl⟩⟩

/-- Replicated binder domains shift, rather than erase, the ambient context. -/
theorem multibinders_retain_ambient_context (state : State) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [expr] (.multiLambda 2 [] (.bvar 2)) (.arrow (.multiBinder nameType) expr))}
      (.complete state [Effects.boolean true] [] []) ∧
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [expr] (.multiLambda 2 [] (.bvar 2)) (.arrow (.multiBinder nameType) nameType))}
      (.complete state [Effects.boolean false] [] []) :=
  ⟨(check_has_type_derivation_iff language [] [expr] (.multiLambda 2 [] (.bvar 2))
      (.arrow (.multiBinder nameType) expr) state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩,
   (check_has_type_derivation_iff language [] [expr] (.multiLambda 2 [] (.bvar 2))
      (.arrow (.multiBinder nameType) nameType) state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩⟩

/-- Bare authored collections retain the declaration's kind and refuse rest metadata. -/
theorem authored_collection_kind_and_rest (state : State) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.collection .vec [.apply "zero" []] none) (.base "Expressions"))}
      (.complete state [Effects.boolean true] [] []) ∧
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.collection .hashBag [.apply "zero" []] none) (.base "Expressions"))}
      (.complete state [Effects.boolean false] [] []) ∧
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.collection .vec [.apply "zero" []] (some "tail")) (.base "Expressions"))}
      (.complete state [Effects.boolean false] [] []) :=
  ⟨(check_has_type_derivation_iff language [] [] (.collection .vec [.apply "zero" []] none)
      (.base "Expressions") state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩,
   (check_has_type_derivation_iff language [] [] (.collection .hashBag [.apply "zero" []] none)
      (.base "Expressions") state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩,
   (check_has_type_derivation_iff language [] [] (.collection .vec [.apply "zero" []] (some "tail"))
      (.base "Expressions") state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩⟩

/-- A body's type does not override its constructor parameter representation. -/
theorem named_parameter_representation_is_checked (state : State) :
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.apply "binding" [.lambda none (.apply "zero" [])]) expr)}
      (.complete state [Effects.boolean true] [] []) ∧
    DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [] (.apply "binding" [.lambda (some "display") (.apply "zero" [])]) expr)}
      (.complete state [Effects.boolean false] [] []) :=
  ⟨(check_has_type_derivation_iff language [] [] (.apply "binding" [.lambda none (.apply "zero" [])])
      expr state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩,
   (check_has_type_derivation_iff language [] [] (.apply "binding" [.lambda (some "display") (.apply "zero" [])])
      expr state state _ [] []).mpr ⟨rfl,by decide +kernel,rfl,rfl⟩⟩

/-- An out-of-range index cannot acquire an accepting derivation. -/
theorem absent_bound_index_cannot_accept (state : State) :
    ¬ DeclarativeSpec.Runs program {state,control := .evaluate [] (query language [] [expr] (.bvar 1) expr)}
      (.complete state [Effects.boolean true] [] []) := by
  intro accepted
  have observation := (check_has_type_derivation_iff language [] [expr] (.bvar 1) expr state state _ [] []).mp accepted
  have impossible : [Effects.boolean true] ≠
      [Effects.boolean (checkHasType language (FreeTypeContext.ofList []) [expr] (.bvar 1) expr)] := by
    decide +kernel
  exact impossible observation.2.1

end SourceControls

#print axioms SourceControls.later_declaration_is_checked
#print axioms SourceControls.free_context_first_shadow
#print axioms SourceControls.multibinders_retain_ambient_context
#print axioms SourceControls.authored_collection_kind_and_rest
#print axioms SourceControls.named_parameter_representation_is_checked
#print axioms SourceControls.absent_bound_index_cannot_accept

end DeclarationTyping

namespace OpenAdmission

open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem symbol_pattern_mismatch (caller : Subst) (head : String) (pattern : Pattern) :
    SpaceSemantics.matchValue caller (.symbol head) (patternValue pattern) = none := by
  rw [SpaceSemantics.matchValue_literal (SpaceSemantics.Literal.symbol head)]
  cases pattern <;> simp [InferenceCettaWire.encodePattern, CettaWireAtom.encode]

attribute [local simp] symbol_pattern_mismatch

private theorem object_list_from_elements (state : State) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a "gslt:premise:object-pattern" [patternValue pattern]) state
      (Effects.boolean (isObjectPattern pattern))) :
    PureReturns program [] state (a "gslt:premise:object-patterns" [patternsValue patterns]) state
      (Effects.boolean (isObjectPatternList patterns)) := by
  induction patterns with
  | nil =>
      apply unary_case_returns .objectPatterns state (patternsValue [])
        (unaryEnvironment .objectPatterns (patternsValue [])) (Effects.boolean true)
      · simp [UnaryHelper.cases, flagListCases, patternsValue, InferenceCettaWire.encodePatterns,
          encoded, CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program _ state (.bool true)
  | cons pattern patterns ih =>
      let caller := unaryEnvironment .objectPatterns (patternsValue (pattern :: patterns))
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      apply unary_case_returns .objectPatterns state (patternsValue (pattern :: patterns))
        selected (flagListCons "gslt:premise:object-pattern" "gslt:premise:object-patterns")
      · simp [UnaryHelper.cases, flagListCases, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply QuantifiedLocal.bool_if_returns selected state _ (isObjectPattern pattern) _ _ _
        · exact unary_capture .objectPattern selected state (patternValue pattern) (v "pattern") _
            (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
            (elements pattern (by simp))
        · cases value : isObjectPattern pattern with
          | false =>
              simpa [flagListCons, isObjectPatternList, value, Effects.boolean] using
                grounded_returns program selected state (.bool false)
          | true =>
              simpa [flagListCons, isObjectPatternList, value, UnaryHelper.head] using
                unary_capture .objectPatterns selected state (patternsValue patterns) (v "rest") _
                  (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
                  (ih (fun child member => elements child (List.mem_cons_of_mem _ member)))

/-- Actual source traversal checks the original object-form predicate on
all Pattern constructors, including schema forms that must be refused. -/
theorem object_pattern_returns (state : State) (pattern : Pattern) :
    PureReturns program [] state (a "gslt:premise:object-pattern" [patternValue pattern]) state
      (Effects.boolean (isObjectPattern pattern)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let caller := unaryEnvironment .objectPattern (patternValue (.bvar index))
      let selected := ("index", encoded (.natural index)) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.bvar index)) selected (Effects.boolean true)
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact grounded_returns program selected state (.bool true)
  | hfvar name =>
      let caller := unaryEnvironment .objectPattern (patternValue (.fvar name))
      let selected := ("name", encoded (.string name)) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.fvar name)) selected (Effects.boolean true)
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact grounded_returns program selected state (.bool true)
  | happly label arguments ih =>
      let caller := unaryEnvironment .objectPattern (patternValue (.apply label arguments))
      let selected := ("arguments", patternsValue arguments) :: ("label", encoded (.string label)) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.apply label arguments)) selected
        (a "gslt:premise:object-patterns" [v "arguments"])
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact unary_capture .objectPatterns selected state (patternsValue arguments) (v "arguments") _
          (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
          (object_list_from_elements state arguments ih)
  | hlambda binder body ih =>
      let caller := unaryEnvironment .objectPattern (patternValue (.lambda binder body))
      let selected := ("body", patternValue body) :: ("binder", encoded (InferenceCettaWire.encodeBinder binder)) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.lambda binder body)) selected
        (a "gslt:premise:object-pattern" [v "body"])
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact unary_capture .objectPattern selected state (patternValue body) (v "body") _
          (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) ih
  | hmultiLambda arity binders body ih =>
      let caller := unaryEnvironment .objectPattern (patternValue (.multiLambda arity binders body))
      let selected := ("body", patternValue body) ::
        ("binders", encoded (InferenceCettaWire.encodeList Term.string binders)) ::
        ("arity", encoded (.natural arity)) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.multiLambda arity binders body)) selected
        (a "gslt:premise:object-pattern" [v "body"])
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact unary_capture .objectPattern selected state (patternValue body) (v "body") _
          (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) ih
  | hsubst body replacement _ _ =>
      let caller := unaryEnvironment .objectPattern (patternValue (.subst body replacement))
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      apply unary_case_returns .objectPattern state (patternValue (.subst body replacement)) selected (Effects.boolean false)
      · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact grounded_returns program selected state (.bool false)
  | hcollection kind elements rest ih =>
      cases rest with
      | none =>
          let caller := unaryEnvironment .objectPattern (patternValue (.collection kind elements none))
          let selected := ("elements", patternsValue elements) ::
            ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
          simp only [isObjectPattern, Option.isNone_none, Bool.true_and]
          apply unary_case_returns .objectPattern state (patternValue (.collection kind elements none)) selected
            (a "gslt:premise:object-patterns" [v "elements"])
          · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
          · exact unary_capture .objectPatterns selected state (patternsValue elements) (v "elements") _
              (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
              (object_list_from_elements state elements ih)
      | some name =>
          let value := patternValue (.collection kind elements (some name))
          let selected := ("bad", value) :: unaryEnvironment .objectPattern value
          simp only [isObjectPattern, Option.isNone_some, Bool.false_and]
          apply unary_case_returns .objectPattern state value selected (Effects.boolean false)
          · simp [UnaryHelper.cases, objectCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeRest, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, value, unaryEnvironment, UnaryHelper.formal]
          · exact grounded_returns program selected state (.bool false)

theorem object_patterns_returns (state : State) (patterns : List Pattern) :
    PureReturns program [] state (a "gslt:premise:object-patterns" [patternsValue patterns]) state
      (Effects.boolean (isObjectPatternList patterns)) :=
  object_list_from_elements state patterns (fun pattern _ => object_pattern_returns state pattern)

theorem object_pattern_captured_returns (caller : Subst) (state : State)
    (pattern : Pattern) (input : Atom) (captured : applySubst caller input = patternValue pattern) :
    PureReturns program caller state (a "gslt:premise:object-pattern" [input]) state
      (Effects.boolean (isObjectPattern pattern)) :=
  unary_capture .objectPattern caller state _ _ _ captured (object_pattern_returns state pattern)

#print axioms object_pattern_returns
#print axioms object_patterns_returns
#print axioms object_pattern_captured_returns

private theorem canonical_list_from_elements (state : State) (patterns : List Pattern)
    (elements : ∀ pattern ∈ patterns, PureReturns program [] state
      (a "gslt:premise:canonical-binders" [patternValue pattern]) state
      (Effects.boolean (Pattern.hasCanonicalBinderMetadata pattern))) :
    PureReturns program [] state (a "gslt:premise:canonical-binders-list" [patternsValue patterns]) state
      (Effects.boolean (Pattern.hasCanonicalBinderMetadataList patterns)) := by
  induction patterns with
  | nil =>
      apply unary_case_returns .canonicalPatterns state (patternsValue [])
        (unaryEnvironment .canonicalPatterns (patternsValue [])) (Effects.boolean true)
      · simp [UnaryHelper.cases, flagListCases, patternsValue, InferenceCettaWire.encodePatterns,
          encoded, CettaWireAtom.encode, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program _ state (.bool true)
  | cons pattern patterns ih =>
      let caller := unaryEnvironment .canonicalPatterns (patternsValue (pattern :: patterns))
      let selected := ("rest", patternsValue patterns) :: ("pattern", patternValue pattern) :: caller
      apply unary_case_returns .canonicalPatterns state (patternsValue (pattern :: patterns))
        selected (flagListCons "gslt:premise:canonical-binders" "gslt:premise:canonical-binders-list")
      · simp [UnaryHelper.cases, flagListCases, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply QuantifiedLocal.bool_if_returns selected state _ (Pattern.hasCanonicalBinderMetadata pattern) _ _ _
        · exact unary_capture .canonicalPattern selected state (patternValue pattern) (v "pattern") _
            (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
            (elements pattern (by simp))
        · cases value : Pattern.hasCanonicalBinderMetadata pattern with
          | false =>
              simpa [flagListCons, Pattern.hasCanonicalBinderMetadataList, value, Effects.boolean] using
                grounded_returns program selected state (.bool false)
          | true =>
              simpa [flagListCons, Pattern.hasCanonicalBinderMetadataList, value, UnaryHelper.head] using
                unary_capture .canonicalPatterns selected state (patternsValue patterns) (v "rest") _
                  (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
                  (ih (fun child member => elements child (List.mem_cons_of_mem _ member)))

/-- Actual source traversal agrees with the existing canonical locally nameless
binder metadata predicate; display names are inspected without evaluating data. -/
theorem canonical_binders_returns (state : State) (pattern : Pattern) :
    PureReturns program [] state (a "gslt:premise:canonical-binders" [patternValue pattern]) state
      (Effects.boolean pattern.hasCanonicalBinderMetadata) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      let caller := unaryEnvironment .canonicalPattern (patternValue (.bvar index))
      let selected := ("index", encoded (.natural index)) :: caller
      apply unary_case_returns .canonicalPattern state (patternValue (.bvar index)) selected (Effects.boolean true)
      · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact grounded_returns program selected state (.bool true)
  | hfvar name =>
      let caller := unaryEnvironment .canonicalPattern (patternValue (.fvar name))
      let selected := ("name", encoded (.string name)) :: caller
      apply unary_case_returns .canonicalPattern state (patternValue (.fvar name)) selected (Effects.boolean true)
      · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact grounded_returns program selected state (.bool true)
  | happly label arguments ih =>
      let caller := unaryEnvironment .canonicalPattern (patternValue (.apply label arguments))
      let selected := ("arguments", patternsValue arguments) :: ("label", encoded (.string label)) :: caller
      apply unary_case_returns .canonicalPattern state (patternValue (.apply label arguments)) selected
        (a "gslt:premise:canonical-binders-list" [v "arguments"])
      · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact unary_capture .canonicalPatterns selected state (patternsValue arguments) (v "arguments") _
          (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
          (canonical_list_from_elements state arguments ih)
  | hlambda binder body ih =>
      cases binder with
      | none =>
          let caller := unaryEnvironment .canonicalPattern (patternValue (.lambda none body))
          let selected := ("body", patternValue body) :: caller
          simp only [Pattern.hasCanonicalBinderMetadata, Option.isNone_none, Bool.true_and]
          apply unary_case_returns .canonicalPattern state (patternValue (.lambda none body)) selected
            (a "gslt:premise:canonical-binders" [v "body"])
          · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeBinder, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
          · exact unary_capture .canonicalPattern selected state (patternValue body) (v "body") _
              (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) ih
      | some name =>
          let value := patternValue (.lambda (some name) body)
          let selected := ("bad", value) :: unaryEnvironment .canonicalPattern value
          simp only [Pattern.hasCanonicalBinderMetadata, Option.isNone_some, Bool.false_and]
          apply unary_case_returns .canonicalPattern state value selected (Effects.boolean false)
          · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeBinder, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, value, unaryEnvironment, UnaryHelper.formal]
          · exact grounded_returns program selected state (.bool false)
  | hmultiLambda arity binders body ih =>
      cases binders with
      | nil =>
          let caller := unaryEnvironment .canonicalPattern (patternValue (.multiLambda arity [] body))
          let selected := ("body", patternValue body) :: ("arity", encoded (.natural arity)) :: caller
          simp only [Pattern.hasCanonicalBinderMetadata, List.isEmpty_nil, Bool.true_and]
          apply unary_case_returns .canonicalPattern state (patternValue (.multiLambda arity [] body)) selected
            (a "gslt:premise:canonical-binders" [v "body"])
          · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
          · exact unary_capture .canonicalPattern selected state (patternValue body) (v "body") _
              (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) ih
      | cons name names =>
          let value := patternValue (.multiLambda arity (name :: names) body)
          let selected := ("bad", value) :: unaryEnvironment .canonicalPattern value
          simp only [Pattern.hasCanonicalBinderMetadata, List.isEmpty_cons, Bool.false_and]
          apply unary_case_returns .canonicalPattern state value selected (Effects.boolean false)
          · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
              InferenceCettaWire.encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
              TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match, Subst.lookup, selected, value, unaryEnvironment, UnaryHelper.formal]
          · exact grounded_returns program selected state (.bool false)
  | hsubst body replacement bodyIH replacementIH =>
      let caller := unaryEnvironment .canonicalPattern (patternValue (.subst body replacement))
      let selected := ("replacement", patternValue replacement) :: ("body", patternValue body) :: caller
      apply unary_case_returns .canonicalPattern state (patternValue (.subst body replacement)) selected
        (a "if" [a "gslt:premise:canonical-binders" [v "body"],
          a "gslt:premise:canonical-binders" [v "replacement"], Effects.boolean false])
      · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · apply QuantifiedLocal.bool_if_returns selected state _ body.hasCanonicalBinderMetadata _ _ _
        · exact unary_capture .canonicalPattern selected state (patternValue body) (v "body") _
            (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) bodyIH
        · cases value : body.hasCanonicalBinderMetadata with
          | false =>
              simpa [Pattern.hasCanonicalBinderMetadata, value, Effects.boolean] using
                grounded_returns program selected state (.bool false)
          | true =>
              simpa [Pattern.hasCanonicalBinderMetadata, value, UnaryHelper.head] using
                unary_capture .canonicalPattern selected state (patternValue replacement) (v "replacement") _
                  (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup]) replacementIH
  | hcollection kind elements rest ih =>
      let caller := unaryEnvironment .canonicalPattern (patternValue (.collection kind elements rest))
      let selected := ("rest", encoded (InferenceCettaWire.encodeRest rest)) ::
        ("elements", patternsValue elements) :: ("kind", encoded (InferenceCettaWire.encodeCollectionType kind)) :: caller
      apply unary_case_returns .canonicalPattern state (patternValue (.collection kind elements rest)) selected
        (a "gslt:premise:canonical-binders-list" [v "elements"])
      · simp [UnaryHelper.cases, canonicalCases, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue.matchValues, TypedParameters.representation_constructor_match,
          TypedParameters.representation_symbol_match, TypedParameters.representation_variable_match,
          Subst.lookup, selected, caller, unaryEnvironment, UnaryHelper.formal]
      · exact unary_capture .canonicalPatterns selected state (patternsValue elements) (v "elements") _
          (by simp [selected, caller, unaryEnvironment, UnaryHelper.formal, applySubst, Subst.lookup])
          (canonical_list_from_elements state elements ih)

theorem canonical_binders_list_returns (state : State) (patterns : List Pattern) :
    PureReturns program [] state (a "gslt:premise:canonical-binders-list" [patternsValue patterns]) state
      (Effects.boolean (Pattern.hasCanonicalBinderMetadataList patterns)) :=
  canonical_list_from_elements state patterns (fun pattern _ => canonical_binders_returns state pattern)

theorem canonical_binders_captured_returns (caller : Subst) (state : State)
    (pattern : Pattern) (input : Atom) (captured : applySubst caller input = patternValue pattern) :
    PureReturns program caller state (a "gslt:premise:canonical-binders" [input]) state
      (Effects.boolean pattern.hasCanonicalBinderMetadata) :=
  unary_capture .canonicalPattern caller state _ _ _ captured (canonical_binders_returns state pattern)

#print axioms canonical_binders_returns
#print axioms canonical_binders_list_returns
#print axioms canonical_binders_captured_returns

end OpenAdmission

namespace DeclarationTyping

private def openBody : Atom :=
  a "if" [a "gslt:premise:type-has"
    [v "declarations", v "free", v "bound", v "pattern", v "expected"],
    a "if" [a "gslt:premise:canonical-binders" [v "pattern"],
      a "if" [a "gslt:premise:object-pattern" [v "pattern"],
        a "let" [v "depth", a "gslt:automata:length" [v "bound"],
          a "gslt:rule:scope-well-scoped" [v "depth", v "pattern"]],
        Effects.boolean false], Effects.boolean false], Effects.boolean false]

private theorem open_shape : (rawEquation .open).body = openBody := by
  decide +kernel

/-- The native admission call carries declarations and both typing contexts.
Display metadata, object form and ordinary scope are checked independently. -/
def openQuery (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern) : Atom :=
  a "gslt:premise:open-well-sorted" [declarationsValue language.terms,
    freeValue free, boundValue bound, typeValue expected, patternValue pattern]

theorem check_open_pattern_returns (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state : State) :
    PureReturns program [] state (openQuery language free bound expected pattern) state
      (Effects.boolean (WellSorted.checkOpenPatternWellSorted language
        (WellSorted.FreeTypeContext.ofList free) bound expected pattern)) := by
  let values := [declarationsValue language.terms, freeValue free, boundValue bound,
    typeValue expected, patternValue pattern]
  let caller := rawEnvironment .open values
  change PureReturns program [] state (a RawHelper.open.head values) state _
  apply raw_closed .open state values _ rfl
  rw [open_shape]
  apply QuantifiedLocal.bool_if_returns caller state _
    (WellSorted.checkHasType language (WellSorted.FreeTypeContext.ofList free) bound pattern expected) _ _ _
  · exact check_has_type_captured_returns caller state language free bound pattern expected
      (v "declarations") (v "free") (v "bound") (v "pattern") (v "expected")
      (by simp [caller, values, rawEnvironment, RawHelper.names, applySubst, Subst.lookup])
  · cases typed : WellSorted.checkHasType language
        (WellSorted.FreeTypeContext.ofList free) bound pattern expected with
    | false =>
        simpa [openBody, WellSorted.checkOpenPatternWellSorted, typed, Effects.boolean] using
          grounded_returns program caller state (.bool false)
    | true =>
        simp only [WellSorted.checkOpenPatternWellSorted, typed, Bool.true_and]
        apply QuantifiedLocal.bool_if_returns caller state _ pattern.hasCanonicalBinderMetadata _ _ _
        · exact OpenAdmission.canonical_binders_captured_returns caller state pattern (v "pattern")
            (by simp [caller, values, rawEnvironment, RawHelper.names, applySubst, Subst.lookup])
        · cases canonical : pattern.hasCanonicalBinderMetadata with
          | false =>
              simpa [canonical, Effects.boolean] using grounded_returns program caller state (.bool false)
          | true =>
              simp only [Bool.true_and]
              apply QuantifiedLocal.bool_if_returns caller state _ (WellSorted.isObjectPattern pattern) _ _ _
              · exact OpenAdmission.object_pattern_captured_returns caller state pattern (v "pattern")
                  (by simp [caller, values, rawEnvironment, RawHelper.names, applySubst, Subst.lookup])
              · cases object : WellSorted.isObjectPattern pattern with
                | false =>
                    simpa [object, Effects.boolean] using grounded_returns program caller state (.bool false)
                | true =>
                    simp only [Bool.true_and, WellSorted.checkScopeSafeAt]
                    apply QuantifiedLocal.named_let_returns caller state "depth" _
                      (encoded (.natural bound.length)) _ _
                    · simp [caller, values, rawEnvironment, RawHelper.names, Subst.lookup]
                    · apply RuleExecutionProgram.automata_captured_returns
                        (by simp [codeWithin, atomsWithin, expressionHeadWithin, RuleExecutionProgram.matcherHead])
                      simpa only [MatchAutomataSourceExecution.listValue, boundValue, boundContextTerm,
                        List.length_map] using
                        MatchAutomataSourceExecution.length_captured_returns caller state
                          (bound.map InferenceCettaWire.AuthoredRule.typeTerm) (v "bound")
                          (by simp [caller, values, rawEnvironment, RawHelper.names, applySubst,
                            Subst.lookup, boundValue, boundContextTerm, encodeList_map])
                    · exact RuleInstantiationExecution.ScopedCapture.well_scoped_captured_returns
                        (("depth", encoded (.natural bound.length)) :: caller) state pattern bound.length
                        (v "depth") (v "pattern")
                        (by simp [caller, values, rawEnvironment, RawHelper.names, applySubst, Subst.lookup])

theorem check_open_pattern_captured_returns (caller : Subst) (state : State)
    (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (one two three four five : Atom)
    (captured : [one, two, three, four, five].map (applySubst caller) =
      [declarationsValue language.terms, freeValue free, boundValue bound,
        typeValue expected, patternValue pattern]) :
    PureReturns program caller state
      (a "gslt:premise:open-well-sorted" [one, two, three, four, five]) state
      (Effects.boolean (WellSorted.checkOpenPatternWellSorted language
        (WellSorted.FreeTypeContext.ofList free) bound expected pattern)) :=
  raw_capture .open caller state _ _ _ rfl captured
    (check_open_pattern_returns language free bound expected pattern state)

theorem check_open_pattern_completed_iff (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state after : State)
    (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := (.evaluate []
      (openQuery language free bound expected pattern))} = .complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (WellSorted.checkOpenPatternWellSorted
        language (WellSorted.FreeTypeContext.ofList free) bound expected pattern)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (check_open_pattern_returns language free bound expected pattern state) after answers input output

theorem check_open_pattern_derivation_iff (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state after : State)
    (answers input output : List Atom) :
    DeclarativeSpec.Runs program {state, control := (.evaluate []
      (openQuery language free bound expected pattern))} (.complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (WellSorted.checkOpenPatternWellSorted
        language (WellSorted.FreeTypeContext.ofList free) bound expected pattern)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (check_open_pattern_returns language free bound expected pattern state) after answers input output

theorem accepted_open_pattern_iff (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state : State) :
    DeclarativeSpec.Runs program {state, control := (.evaluate []
      (openQuery language free bound expected pattern))}
      (.complete state [Effects.boolean true] [] []) ↔
      WellSorted.OpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList free)
        bound expected pattern := by
  rw [check_open_pattern_derivation_iff]
  simp only [true_and, and_true, List.cons.injEq, and_true]
  have boolean_same : Effects.boolean true = Effects.boolean
      (WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList free)
        bound expected pattern) ↔
      WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList free)
        bound expected pattern = true := by
    cases WellSorted.checkOpenPatternWellSorted language (WellSorted.FreeTypeContext.ofList free)
      bound expected pattern <;> decide +kernel
  exact boolean_same.trans (WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _)

#print axioms check_open_pattern_returns
#print axioms check_open_pattern_captured_returns
#print axioms check_open_pattern_completed_iff
#print axioms check_open_pattern_derivation_iff
#print axioms accepted_open_pattern_iff

/- The native representation needs only the declarations of free names that
occur in this pattern; the source context itself may be arbitrary. -/
theorem check_open_pattern_finite_free_returns (language : LanguageDef)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state : State) :
    PureReturns program [] state
      (openQuery language (free.entriesOn pattern.freeFvarNames) bound expected pattern) state
      (Effects.boolean (WellSorted.checkOpenPatternWellSorted language free bound expected pattern)) := by
  simpa only [WellSorted.checkOpenPatternWellSorted_finiteFree] using
    check_open_pattern_returns language (free.entriesOn pattern.freeFvarNames) bound expected pattern state

theorem accepted_open_pattern_finite_free_iff (language : LanguageDef)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (pattern : Pattern) (state : State) :
    DeclarativeSpec.Runs program {state, control := (.evaluate []
      (openQuery language (free.entriesOn pattern.freeFvarNames) bound expected pattern))}
      (.complete state [Effects.boolean true] [] []) ↔
      WellSorted.OpenPatternWellSorted language free bound expected pattern := by
  rw [check_open_pattern_derivation_iff]
  rw [WellSorted.checkOpenPatternWellSorted_finiteFree]
  simp only [true_and, and_true, List.cons.injEq, and_true]
  have boolean_same : Effects.boolean true = Effects.boolean
      (WellSorted.checkOpenPatternWellSorted language free bound expected pattern) ↔
      WellSorted.checkOpenPatternWellSorted language free bound expected pattern = true := by
    cases WellSorted.checkOpenPatternWellSorted language free bound expected pattern <;> decide +kernel
  exact boolean_same.trans (WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _)

#print axioms check_open_pattern_finite_free_returns
#print axioms accepted_open_pattern_finite_free_iff

end DeclarationTyping

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution
