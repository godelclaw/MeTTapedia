import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider

/-!
# Finite relation-tuple matching through retained rule equations

The source operations match the variable arguments of an admitted relation
premise against literal tuple payloads. Argument matching returns a relative
extension; tuple matching then merges that extension with the original seed.
Canonical merge order, conflicting bindings and duplicate tuple occurrences
remain observable. These operations consume supplied finite tuple data and do
not establish a provider, authority or revision contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval RuleExecutionProgram
open MatchAutomataBindingExecution (bindingsTerm bindingTerm patternOptionTerm bindingsOptionTerm)

/-- Variable names retain the canonical ordered list wire. -/
def namesTerm (names : List String) : Term := encodeList .string names

/-- Provider tuples remain literal ordered canonical pattern rows. -/
def tuplesTerm (tuples : List (List Pattern)) : Term :=
  encodeList InferenceCettaWire.encodePatterns tuples

/-- Each matching occurrence contributes a distinct ordered binding result. -/
def bindingResultsTerm (results : List Bindings) : Term := encodeList bindingsTerm results

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)
private abbrev patternsValue (patterns : List Pattern) : Atom := encoded (InferenceCettaWire.encodePatterns patterns)
private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (bindingsTerm bindings)
private abbrev optionValue (bindings : Option Bindings) : Atom := encoded (bindingsOptionTerm bindings)
private abbrev namesValue (names : List String) : Atom := encoded (namesTerm names)
private abbrev tuplesValue (tuples : List (List Pattern)) : Atom := encoded (tuplesTerm tuples)
private abbrev resultsValue (results : List Bindings) : Atom := encoded (bindingResultsTerm results)

attribute [local simp] a v encoded patternValue patternsValue bindingsValue optionValue namesValue tuplesValue resultsValue

private inductive Helper where | argument | arguments | tuple | tuples
private def Helper.head : Helper → String
  | .argument => "gslt:rule:relation-argument"
  | .arguments => "gslt:rule:relation-arguments"
  | .tuple => "gslt:rule:match-tuple"
  | .tuples => "gslt:rule:match-tuples"
private def Helper.first : Helper → String
  | .argument => "name"
  | _ => "names"
private def Helper.second : Helper → String
  | .argument => "value"
  | .tuples => "tuples"
  | _ => "values"
private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (first second : Atom) (seed : Bindings) : Subst :=
  [("seed", bindingsValue seed), (helper.second, second), (helper.first, first)]

private theorem helper_clause (helper : Helper) (first second : Atom) (seed : Bindings) :
    clauses program helper.head [first, second, bindingsValue seed] =
      [.evaluate (environment helper first second seed) (equation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [equation helper] from by cases helper <;> rfl]
  have formals : (equation helper).arguments = [v helper.first, v helper.second, v "seed"] := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, environment, Helper.first, Helper.second,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (first second : Atom) (seed : Bindings) (one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [first, second, bindingsValue seed])
    (returned : PureReturns program (environment helper first second seed) state
      (equation helper).body state answer) :
    PureReturns program caller state (a helper.head [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller (environment helper first second seed) state state
    helper.head [one, two, three] (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact helper_clause helper first second seed

private def optionCases (name : String) (absent present : Atom) : SpaceSemantics.Cases :=
  [(.symbol "None", absent), (a "Some" [v name], present)]
private def optionCase (name : String) (expression absent present : Atom) : Atom :=
  a "case" [expression, .expression ((optionCases name absent present).map fun row => .expression [row.1, row.2])]

private theorem none_case_returns (caller : Subst) (state : State) (name : String)
    (expression absent present answer : Atom)
    (evaluated : PureReturns program caller state expression state (.symbol "None"))
    (returned : PureReturns program caller state absent state answer) :
    PureReturns program caller state (optionCase name expression absent present) state answer := by
  apply case_returns program caller caller state state state expression (.symbol "None") absent answer _
    (optionCases name absent present) (read_cases_encoded _) evaluated _ returned
  simp [optionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]

private theorem some_case_returns (caller : Subst) (state : State) (name : String)
    (expression absent present payload answer : Atom)
    (fresh : Subst.lookup caller name = none)
    (evaluated : PureReturns program caller state expression state (a "Some" [payload]))
    (returned : PureReturns program ((name, payload) :: caller) state present state answer) :
    PureReturns program caller state (optionCase name expression absent present) state answer := by
  apply case_returns program caller ((name, payload) :: caller) state state state expression
    (a "Some" [payload]) present answer _ (optionCases name absent present) (read_cases_encoded _)
    evaluated _ returned
  simp [optionCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, fresh]

private theorem merge_captured (caller : Subst) (state : State) (left right : Bindings)
    (one two : String) (captured : [v one, v two].map (applySubst caller) = [bindingsValue left, bindingsValue right]) :
    PureReturns program caller state (a "gslt:automata:merge" [v one, v two]) state
      (optionValue (mergeBindings left right)) :=
  automata_captured_returns (by simp [codeWithin, atomsWithin, expressionHeadWithin, matcherHead])
    (MatchAutomataBindingExecution.merge_captured_returns caller state left right _ captured)

private def argumentMissing : Atom := a "Some" [a "LCons" [a "Binding" [v "name", v "value"], .symbol "LNil"]]
private def argumentFound : Atom := a "if" [a "==" [v "prior", v "value"], a "Some" [.symbol "LNil"], .symbol "None"]
private def argumentBody : Atom := optionCase "prior"
  (a "gslt:automata:binding" [v "name", v "seed"]) argumentMissing argumentFound

private def argumentsTail : Atom := optionCase "tail"
  (a "gslt:rule:relation-arguments" [v "names-rest", v "values-rest", v "extended"])
  (.symbol "None") (a "gslt:automata:merge" [v "head", v "tail"])
private def argumentsExtended : Atom := optionCase "extended"
  (a "gslt:automata:merge" [v "seed", v "head"]) (.symbol "None") argumentsTail
private def argumentsCons : Atom := optionCase "head"
  (a "gslt:rule:relation-argument" [v "name", v "value", v "seed"])
  (.symbol "None") argumentsExtended
private def argumentsCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], a "Some" [.symbol "LNil"]),
   (.expression [a "LCons" [v "name", v "names-rest"], a "LCons" [v "value", v "values-rest"]], argumentsCons),
   (v "bad", .symbol "None")]
private def tupleBody : Atom := optionCase "extended"
  (a "gslt:rule:relation-arguments" [v "names", v "values", v "seed"])
  (.symbol "None") (a "gslt:automata:merge" [v "seed", v "extended"])
private def tuplesHead : Atom := optionCase "bindings"
  (a "gslt:rule:match-tuple" [v "names", v "values", v "seed"])
  (v "tail") (a "LCons" [v "bindings", v "tail"])
private def tuplesCons : Atom := a "let" [v "tail",
  a "gslt:rule:match-tuples" [v "names", v "rest", v "seed"], tuplesHead]
private def tuplesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "values", v "rest"], tuplesCons)]

private theorem argument_shape : (equation .argument).body = argumentBody := by decide +kernel
private theorem arguments_shape : (equation .arguments).body =
    a "case" [.expression [v "names", v "values"],
      .expression (argumentsCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem tuple_shape : (equation .tuple).body = tupleBody := by decide +kernel
private theorem tuples_shape : (equation .tuples).body =
    a "case" [v "tuples", .expression (tuplesCases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem missing_template : PureData.Template program argumentMissing := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Binding" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .symbol _

private theorem some_nil_returns (caller : Subst) (state : State) :
    PureReturns program caller state (a "Some" [.symbol "LNil"]) state (a "Some" [.symbol "LNil"]) := by
  have literal : PureData.Template program (a "Some" [.symbol "LNil"]) := by
    apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .symbol _
  simpa [applySubst, applySubst.applySubstList] using
    PureData.template_return program caller state _ literal

private theorem argument_body_returns (state : State) (seed : Bindings) (name : String) (value : Pattern) :
    PureReturns program (environment .argument (encoded (.string name)) (patternValue value) seed) state
      (equation .argument).body state (optionValue (relationArgument? seed name value)) := by
  let caller := environment .argument (encoded (.string name)) (patternValue value) seed
  have lookedUp := automata_captured_returns (by decide +kernel)
    (MatchAutomataBindingExecution.binding_captured_returns caller state name seed
      [v "name", v "seed"] (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup]))
  rw [argument_shape]
  cases found : seed.lookup name with
  | none =>
      apply none_case_returns caller state "prior" _ argumentMissing argumentFound _
      · simpa [found, patternOptionTerm, CettaWireAtom.encode] using lookedUp
      · simpa [argumentMissing, relationArgument?, found, bindingsOptionTerm, bindingsTerm,
          bindingTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          caller, environment, Helper.first, Helper.second, applySubst,
          applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program caller state _ missing_template
  | some prior =>
      let selected := ("prior", patternValue prior) :: caller
      apply some_case_returns caller state "prior" _ argumentMissing argumentFound
        (patternValue prior) _
      · simp [caller, environment, Helper.first, Helper.second, Subst.lookup]
      · simpa [found, patternOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using lookedUp
      · have tested := CettaWireAtom.equality_captured_returns program selected state
          (InferenceCettaWire.encodePattern prior) (InferenceCettaWire.encodePattern value) "prior" "value"
          (by simp [selected, applySubst, Subst.lookup])
          (by simp [selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
        have exactness : InferenceCettaWire.encodePattern prior = InferenceCettaWire.encodePattern value ↔
            prior = value := InferenceCettaWire.encodePattern_injective.eq_iff
        simp only [exactness] at tested
        apply if_returns program selected state state state _ _ _ _ _ tested
        by_cases same : prior = value
        · simpa [argumentFound, relationArgument?, found, same, bindingsOptionTerm, bindingsTerm, encodeList,
            CettaWireAtom.encode, CettaWireAtom.encodeMany] using some_nil_returns selected state
        · simpa [argumentFound, relationArgument?, found, same, bindingsOptionTerm, CettaWireAtom.encode,
            Effects.boolean] using
            symbol_returns program selected state "None"

/-- One relation variable yields a relative extension or a consistency refusal. -/
theorem relation_argument_captured_returns (caller : Subst) (state : State) (seed : Bindings)
    (name : String) (value : Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [encoded (.string name), patternValue value, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:relation-argument" [one, two, three]) state
      (optionValue (relationArgument? seed name value)) :=
  helper_call .argument caller state _ _ seed one two three _ captured
    (argument_body_returns state seed name value)

theorem relation_argument_returns (state : State) (seed : Bindings) (name : String) (value : Pattern) :
    PureReturns program [] state
      (a "gslt:rule:relation-argument" [encoded (.string name), patternValue value, bindingsValue seed]) state
      (optionValue (relationArgument? seed name value)) :=
  relation_argument_captured_returns [] state seed name value _ _ _ (by simp)

private theorem argument_pair_returns (caller : Subst) (state : State) (names : List String) (values : List Pattern)
    (left : applySubst caller (v "names") = namesValue names)
    (right : applySubst caller (v "values") = patternsValue values) :
    PureReturns program caller state (.expression [v "names", v "values"]) state
      (.expression [namesValue names, patternsValue values]) := by
  refine .step (step_transition rfl) ?_
  apply PureData.arguments_return program caller state _ _ _ [] 0
  exact .cons (by simpa [left] using variable_returns program caller state "names")
    (.cons (by simpa [right] using variable_returns program caller state "values") .nil)

private theorem arguments_body_returns (state : State) (seed : Bindings) (names : List String)
    (values : List Pattern) :
    PureReturns program (environment .arguments (namesValue names) (patternsValue values) seed) state
      (equation .arguments).body state (optionValue (relationArguments? seed names values)) := by
  induction names generalizing seed values with
  | nil =>
      cases values with
      | nil =>
          let caller := environment .arguments (namesValue []) (patternsValue []) seed
          rw [arguments_shape]
          apply case_returns program caller caller state state state
            (.expression [v "names", v "values"]) (.expression [.symbol "LNil", .symbol "LNil"])
            (a "Some" [.symbol "LNil"]) _ _ argumentsCases (read_cases_encoded _) _ _ _
          · simpa [namesTerm, encodeList, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
              argument_pair_returns caller state [] []
                (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
                (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          · simp [argumentsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom]
          · simpa [relationArguments?, bindingsOptionTerm, bindingsTerm, encodeList,
              CettaWireAtom.encode, CettaWireAtom.encodeMany] using some_nil_returns caller state
      | cons value values =>
          let caller := environment .arguments (namesValue []) (patternsValue (value :: values)) seed
          let selected := ("bad", .expression [namesValue [], patternsValue (value :: values)]) :: caller
          rw [arguments_shape]
          apply case_returns program caller selected state state state
            (.expression [v "names", v "values"])
            (.expression [namesValue [], patternsValue (value :: values)]) (.symbol "None") _ _
            argumentsCases (read_cases_encoded _) _ _ _
          · exact argument_pair_returns caller state [] (value :: values)
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          · simp [argumentsCases, namesTerm, encodeList, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
          · simpa [relationArguments?, bindingsOptionTerm, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
  | cons name names ih =>
      cases values with
      | nil =>
          let caller := environment .arguments (namesValue (name :: names)) (patternsValue []) seed
          let selected := ("bad", .expression [namesValue (name :: names), patternsValue []]) :: caller
          rw [arguments_shape]
          apply case_returns program caller selected state state state
            (.expression [v "names", v "values"])
            (.expression [namesValue (name :: names), patternsValue []]) (.symbol "None") _ _
            argumentsCases (read_cases_encoded _) _ _ _
          · exact argument_pair_returns caller state (name :: names) []
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          · simp [argumentsCases, namesTerm, encodeList, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
          · simpa [relationArguments?, bindingsOptionTerm, CettaWireAtom.encode] using
              symbol_returns program selected state "None"
      | cons value values =>
          let caller := environment .arguments (namesValue (name :: names)) (patternsValue (value :: values)) seed
          let selected := ("values-rest", patternsValue values) :: ("value", patternValue value) ::
            ("names-rest", namesValue names) :: ("name", encoded (.string name)) :: caller
          have headReturned := relation_argument_captured_returns selected state seed name value
            (v "name") (v "value") (v "seed")
            (by simp [selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          rw [arguments_shape]
          apply case_returns program caller selected state state state
            (.expression [v "names", v "values"])
            (.expression [namesValue (name :: names), patternsValue (value :: values)]) argumentsCons _ _
            argumentsCases (read_cases_encoded _) _ _ _
          · exact argument_pair_returns caller state (name :: names) (value :: values)
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
              (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          · simp [argumentsCases, namesTerm, encodeList, InferenceCettaWire.encodePatterns,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
              SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
              selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
          · cases headFound : relationArgument? seed name value with
            | none =>
                apply none_case_returns selected state "head" _ (.symbol "None") argumentsExtended _
                · simpa [headFound, bindingsOptionTerm, CettaWireAtom.encode] using headReturned
                · simpa [relationArguments?, headFound, bindingsOptionTerm, CettaWireAtom.encode] using
                    symbol_returns program selected state "None"
            | some head =>
                let headBound := ("head", bindingsValue head) :: selected
                apply some_case_returns selected state "head" _ (.symbol "None") argumentsExtended
                  (bindingsValue head) _
                · simp [selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
                · simpa [headFound, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using headReturned
                · have extendedReturned := merge_captured headBound state seed head "seed" "head"
                    (by simp [headBound, selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
                  cases extendedFound : mergeBindings seed head with
                  | none =>
                      apply none_case_returns headBound state "extended" _ (.symbol "None") argumentsTail _
                      · simpa [extendedFound, bindingsOptionTerm, CettaWireAtom.encode] using extendedReturned
                      · simpa [relationArguments?, headFound, extendedFound, bindingsOptionTerm, CettaWireAtom.encode] using
                          symbol_returns program headBound state "None"
                  | some extended =>
                      let extendedBound := ("extended", bindingsValue extended) :: headBound
                      apply some_case_returns headBound state "extended" _ (.symbol "None") argumentsTail
                        (bindingsValue extended) _
                      · simp [headBound, selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
                      · simpa [extendedFound, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using extendedReturned
                      · have tailReturned := helper_call .arguments extendedBound state (namesValue names)
                          (patternsValue values) extended (v "names-rest") (v "values-rest") (v "extended")
                          (optionValue (relationArguments? extended names values))
                          (by simp [extendedBound, headBound, selected, caller, environment, Helper.first, Helper.second,
                            applySubst, Subst.lookup]) (ih extended values)
                        cases tailFound : relationArguments? extended names values with
                        | none =>
                            apply none_case_returns extendedBound state "tail" _ (.symbol "None")
                              (a "gslt:automata:merge" [v "head", v "tail"]) _
                            · simpa [tailFound, bindingsOptionTerm, CettaWireAtom.encode, Helper.head] using tailReturned
                            · simpa [relationArguments?, headFound, extendedFound, tailFound,
                                bindingsOptionTerm, CettaWireAtom.encode] using
                                symbol_returns program extendedBound state "None"
                        | some tail =>
                            let tailBound := ("tail", bindingsValue tail) :: extendedBound
                            apply some_case_returns extendedBound state "tail" _ (.symbol "None")
                              (a "gslt:automata:merge" [v "head", v "tail"]) (bindingsValue tail) _
                            · simp [extendedBound, headBound, selected, caller, environment,
                                Helper.first, Helper.second, Subst.lookup]
                            · simpa [tailFound, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                                Helper.head] using tailReturned
                            · simpa [relationArguments?, headFound, extendedFound, tailFound] using
                                merge_captured tailBound state head tail "head" "tail"
                                  (by simp [tailBound, extendedBound, headBound, applySubst, Subst.lookup])

theorem relation_arguments_captured_returns (caller : Subst) (state : State) (seed : Bindings)
    (names : List String) (values : List Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [namesValue names, patternsValue values, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:relation-arguments" [one, two, three]) state
      (optionValue (relationArguments? seed names values)) :=
  helper_call .arguments caller state _ _ seed one two three _ captured
    (arguments_body_returns state seed names values)

theorem relation_arguments_returns (state : State) (seed : Bindings) (names : List String) (values : List Pattern) :
    PureReturns program [] state
      (a "gslt:rule:relation-arguments" [namesValue names, patternsValue values, bindingsValue seed]) state
      (optionValue (relationArguments? seed names values)) :=
  relation_arguments_captured_returns [] state seed names values _ _ _ (by simp)

private theorem tuple_body_returns (state : State) (seed : Bindings) (plan : PremisePlan) (values : List Pattern) :
    PureReturns program (environment .tuple (namesValue plan.arguments) (patternsValue values) seed) state
      (equation .tuple).body state (optionValue (plan.matchTuple? seed values)) := by
  let caller := environment .tuple (namesValue plan.arguments) (patternsValue values) seed
  have extendedReturned := relation_arguments_captured_returns caller state seed plan.arguments values
    (v "names") (v "values") (v "seed")
    (by simp [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
  rw [tuple_shape]
  cases extendedFound : relationArguments? seed plan.arguments values with
  | none =>
      apply none_case_returns caller state "extended" _ (.symbol "None")
        (a "gslt:automata:merge" [v "seed", v "extended"]) _
      · simpa [extendedFound, bindingsOptionTerm, CettaWireAtom.encode] using extendedReturned
      · simpa [PremisePlan.matchTuple?, extendedFound, bindingsOptionTerm, CettaWireAtom.encode] using
          symbol_returns program caller state "None"
  | some extended =>
      let selected := ("extended", bindingsValue extended) :: caller
      apply some_case_returns caller state "extended" _ (.symbol "None")
        (a "gslt:automata:merge" [v "seed", v "extended"]) (bindingsValue extended) _
      · simp [caller, environment, Helper.first, Helper.second, Subst.lookup]
      · simpa [extendedFound, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using extendedReturned
      · simpa [PremisePlan.matchTuple?, extendedFound] using
          merge_captured selected state seed extended "seed" "extended"
            (by simp [selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])

theorem match_tuple_captured_returns (caller : Subst) (state : State) (seed : Bindings)
    (plan : PremisePlan) (values : List Pattern) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [namesValue plan.arguments, patternsValue values, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:match-tuple" [one, two, three]) state
      (optionValue (plan.matchTuple? seed values)) :=
  helper_call .tuple caller state _ _ seed one two three _ captured
    (tuple_body_returns state seed plan values)

theorem match_tuple_returns (state : State) (seed : Bindings) (plan : PremisePlan) (values : List Pattern) :
    PureReturns program [] state
      (a "gslt:rule:match-tuple" [namesValue plan.arguments, patternsValue values, bindingsValue seed]) state
      (optionValue (plan.matchTuple? seed values)) :=
  match_tuple_captured_returns [] state seed plan values _ _ _ (by simp)

private theorem cons_result_template : PureData.Template program (a "LCons" [v "bindings", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem tuples_body_returns (state : State) (seed : Bindings) (plan : PremisePlan)
    (tuples : List (List Pattern)) :
    PureReturns program (environment .tuples (namesValue plan.arguments) (tuplesValue tuples) seed) state
      (equation .tuples).body state (resultsValue (tuples.filterMap (plan.matchTuple? seed))) := by
  induction tuples with
  | nil =>
      let caller := environment .tuples (namesValue plan.arguments) (.symbol "LNil") seed
      rw [tuples_shape]
      simp only [List.filterMap_nil, tuplesValue, resultsValue, encoded, tuplesTerm,
        bindingResultsTerm, encodeList, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "tuples") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ tuplesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup] using
          variable_returns program caller state "tuples"
      · simp [tuplesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons values rest ih =>
      let caller := environment .tuples (namesValue plan.arguments) (tuplesValue (values :: rest)) seed
      let selected := ("rest", tuplesValue rest) :: ("values", patternsValue values) :: caller
      let tailValue := resultsValue (rest.filterMap (plan.matchTuple? seed))
      let tailBound := ("tail", tailValue) :: selected
      have tailReturned := helper_call .tuples selected state (namesValue plan.arguments) (tuplesValue rest)
        seed (v "names") (v "rest") (v "seed") tailValue
        (by simp [selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup]) ih
      rw [tuples_shape]
      apply case_returns program caller selected state state state (v "tuples")
        (tuplesValue (values :: rest)) tuplesCons _ _ tuplesCases (read_cases_encoded _) _ _ _
      · simpa [caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup] using
          variable_returns program caller state "tuples"
      · simp [tuplesCases, tuplesTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
      · apply let_returns program selected tailBound state state state (v "tail") _ tuplesHead
          tailValue _ tailReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, selected,
            caller, environment, Helper.first, Helper.second]
        · have headReturned := match_tuple_captured_returns tailBound state seed plan values
            (v "names") (v "values") (v "seed")
            (by simp [tailBound, selected, caller, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          cases matched : plan.matchTuple? seed values with
          | none =>
              apply none_case_returns tailBound state "bindings" _ (v "tail")
                (a "LCons" [v "bindings", v "tail"]) _
              · simpa [matched, bindingsOptionTerm, CettaWireAtom.encode] using headReturned
              · simpa [List.filterMap_cons, matched, tailBound, tailValue, applySubst, Subst.lookup] using
                  variable_returns program tailBound state "tail"
          | some bindings =>
              let bound := ("bindings", bindingsValue bindings) :: tailBound
              apply some_case_returns tailBound state "bindings" _ (v "tail")
                (a "LCons" [v "bindings", v "tail"]) (bindingsValue bindings) _
              · simp [tailBound, selected, caller, environment, Helper.first, Helper.second, Subst.lookup]
              · simpa [matched, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using headReturned
              · simpa [List.filterMap_cons, matched, bindingResultsTerm, encodeList,
                  CettaWireAtom.encode, CettaWireAtom.encodeMany, bound, tailBound, tailValue,
                  applySubst, applySubst.applySubstList, Subst.lookup] using
                  PureData.template_return program bound state _ cons_result_template

/-- Finite supplied tuples retain their order and duplicate occurrences. -/
theorem match_tuples_captured_returns (caller : Subst) (state : State) (seed : Bindings)
    (plan : PremisePlan) (tuples : List (List Pattern)) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [namesValue plan.arguments, tuplesValue tuples, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:match-tuples" [one, two, three]) state
      (resultsValue (tuples.filterMap (plan.matchTuple? seed))) :=
  helper_call .tuples caller state _ _ seed one two three _ captured
    (tuples_body_returns state seed plan tuples)

theorem match_tuples_returns (state : State) (seed : Bindings) (plan : PremisePlan) (tuples : List (List Pattern)) :
    PureReturns program [] state
      (a "gslt:rule:match-tuples" [namesValue plan.arguments, tuplesValue tuples, bindingsValue seed]) state
      (resultsValue (tuples.filterMap (plan.matchTuple? seed))) :=
  match_tuples_captured_returns [] state seed plan tuples _ _ _ (by simp)

/-- Tuple execution has the existing canonical premise-matching meaning. -/
theorem match_tuples_canonical_returns (state : State) (seed : Bindings) (plan : PremisePlan)
    (tuples : List (List Pattern)) :
    PureReturns program [] state
      (a "gslt:rule:match-tuples" [namesValue plan.arguments, tuplesValue tuples, bindingsValue seed]) state
      (resultsValue (tuples.flatMap fun tuple =>
        (Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgs seed (plan.arguments.map Pattern.fvar) tuple).filterMap
          (mergeBindings seed))) := by
  rw [← PremisePlan.matchTuples_exact]
  exact match_tuples_returns state seed plan tuples

def matchTuplesQuery (seed : Bindings) (plan : PremisePlan) (tuples : List (List Pattern)) : Atom :=
  a "gslt:rule:match-tuples" [namesValue plan.arguments, tuplesValue tuples, bindingsValue seed]

theorem match_tuples_completed_iff (state : State) (seed : Bindings) (plan : PremisePlan)
    (tuples : List (List Pattern)) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (matchTuplesQuery seed plan tuples) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (tuples.filterMap (plan.matchTuple? seed))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (match_tuples_returns state seed plan tuples)
    after answers input output

theorem match_tuples_derivation_iff (state : State) (seed : Bindings) (plan : PremisePlan)
    (tuples : List (List Pattern)) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (matchTuplesQuery seed plan tuples) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (tuples.filterMap (plan.matchTuple? seed))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (match_tuples_returns state seed plan tuples)
    after answers input output

/-! ## Literal finite provider projection -/

/-- This unscoped view exposes the literal rows of an immutable provider.
Signature availability, argument modes and typed scoped admission remain
separate; this projection does not claim their richer query semantics. -/
def providerTuples (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (relation : String) : List (List Pattern) :=
  rows.filterMap fun row => if row.relation = relation then some row.values else none

def providerEnv (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) :
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv where
  tuples relation _ := providerTuples rows relation

def providerRowTerm (row : Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Term :=
  .application "ProviderRow" [.string row.relation, InferenceCettaWire.encodePatterns row.values]

def providerRowsTerm (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Term :=
  encodeList providerRowTerm rows

private abbrev rowsValue (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Atom :=
  encoded (providerRowsTerm rows)

private def rowsEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:provider-tuples")[0]'(by decide +kernel)

private def rowsEnvironment (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) : Subst :=
  [("rows", rowsValue rows), ("relation", encoded (.string relation))]

private def rowsConsBody : Atom :=
  a "let" [v "tail", a "gslt:rule:provider-tuples" [v "relation", v "rest"],
    a "if" [a "==" [v "relation", v "row-relation"], a "LCons" [v "values", v "tail"], v "tail"]]

private def rowsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "ProviderRow" [v "row-relation", v "values"], v "rest"], rowsConsBody)]

private theorem rows_shape : rowsEquation.body =
    a "case" [v "rows", .expression (rowsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem rows_clause (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) :
    clauses program "gslt:rule:provider-tuples" [encoded (.string relation), rowsValue rows] =
      [.evaluate (rowsEnvironment relation rows) rowsEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:provider-tuples").filterMap _ = _
  rw [show equations "gslt:rule:provider-tuples" = [rowsEquation] from rfl]
  have formals : rowsEquation.arguments = [v "relation", v "rows"] := by decide +kernel
  simp [formals, rowsEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem rows_call (caller : Subst) (state : State) (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (one two answer : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string relation), rowsValue rows])
    (returned : PureReturns program (rowsEnvironment relation rows) state rowsEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:provider-tuples" [one, two]) state answer := by
  apply PureData.raw_authored_call_return program caller (rowsEnvironment relation rows) state state
    "gslt:rule:provider-tuples" [one, two] rowsEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact rows_clause relation rows

private theorem rows_cons_template : PureData.Template program (a "LCons" [v "values", v "tail"]) := by
  apply PureData.Template.constructor
  · decide +kernel
  · decide
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _

private theorem rows_body_returns (state : State) (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) :
    PureReturns program (rowsEnvironment relation rows) state rowsEquation.body state
      (tuplesValue (providerTuples rows relation)) := by
  induction rows with
  | nil =>
      let caller := rowsEnvironment relation []
      rw [rows_shape]
      simp only [providerTuples, List.filterMap_nil, tuplesValue, tuplesTerm, encodeList,
        encoded, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "rows") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ rowsCases (read_cases_encoded _) _ _ _
      · simpa [caller, rowsEnvironment, rowsValue, providerRowsTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "rows"
      · simp [rowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons first rest ih =>
      let caller := rowsEnvironment relation (first :: rest)
      let selected := ("rest", rowsValue rest) :: ("values", patternsValue first.values) ::
        ("row-relation", encoded (.string first.relation)) :: caller
      let tailValue := tuplesValue (providerTuples rest relation)
      let bound := ("tail", tailValue) :: selected
      have tailReturned := rows_call selected state relation rest (v "relation") (v "rest") tailValue
        (by simp [selected, caller, rowsEnvironment, applySubst, Subst.lookup]) ih
      rw [rows_shape]
      apply case_returns program caller selected state state state (v "rows")
        (rowsValue (first :: rest)) rowsConsBody _ _ rowsCases (read_cases_encoded _) _ _ _
      · simpa [caller, rowsEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "rows"
      · simp [rowsCases, rowsValue, providerRowsTerm, providerRowTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, rowsEnvironment, Subst.lookup]
      · apply let_returns program selected bound state state state (v "tail") _
          (a "if" [a "==" [v "relation", v "row-relation"], a "LCons" [v "values", v "tail"], v "tail"])
          tailValue _ tailReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, rowsEnvironment]
        · have tested := CettaWireAtom.equality_captured_returns program bound state
            (.string relation) (.string first.relation) "relation" "row-relation"
            (by simp [bound, selected, caller, rowsEnvironment, applySubst, Subst.lookup])
            (by simp [bound, selected, caller, rowsEnvironment, applySubst, Subst.lookup])
          simp only [Term.string.injEq] at tested
          apply if_returns program bound state state state _ _ _ _ _ tested
          by_cases same : relation = first.relation
          · simpa [providerTuples, List.filterMap_cons, same, tuplesTerm, encodeList,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, Effects.boolean,
              bound, selected, caller, rowsEnvironment, tailValue, applySubst,
              applySubst.applySubstList, Subst.lookup] using
              PureData.template_return program bound state _ rows_cons_template
          · simpa [providerTuples, List.filterMap_cons, Ne.symm same, same, Effects.boolean,
              bound, tailValue, applySubst, Subst.lookup] using variable_returns program bound state "tail"

/-- The actual query walks every finite provider occurrence, retaining exact
relative order and duplicates; equality compares captured names as data. -/
theorem provider_tuples_captured_returns (caller : Subst) (state : State) (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string relation), rowsValue rows]) :
    PureReturns program caller state (a "gslt:rule:provider-tuples" [one, two]) state
      (tuplesValue (providerTuples rows relation)) :=
  rows_call caller state relation rows one two _ captured (rows_body_returns state relation rows)

theorem provider_tuples_returns (state : State) (relation : String)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) :
    PureReturns program [] state
      (a "gslt:rule:provider-tuples" [encoded (.string relation), rowsValue rows]) state
      (tuplesValue (providerTuples rows relation)) :=
  provider_tuples_captured_returns [] state relation rows _ _ (by simp)

/-! ## Canonical argument preparation and builtin tuples -/

private theorem lcons_template {head tail : Atom}
    (headTemplate : PureData.Template program head) (tailTemplate : PureData.Template program tail) :
    PureData.Template program (a "LCons" [head, tail]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact headTemplate
  · exact tailTemplate

private def namesEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:names-patterns")[0]'(by decide +kernel)

private def namesEnvironment (names : List String) : Subst := [("names", namesValue names)]

private def namesConsBody : Atom :=
  a "let" [v "tail", a "gslt:rule:names-patterns" [v "rest"],
    a "LCons" [a "FVar" [v "name"], v "tail"]]

private def namesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "name", v "rest"], namesConsBody)]

private theorem names_shape : namesEquation.body =
    a "case" [v "names", .expression (namesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem names_clause (names : List String) :
    clauses program "gslt:rule:names-patterns" [namesValue names] =
      [.evaluate (namesEnvironment names) namesEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:names-patterns").filterMap _ = _
  rw [show equations "gslt:rule:names-patterns" = [namesEquation] from rfl]
  have formals : namesEquation.arguments = [v "names"] := by decide +kernel
  simp [formals, namesEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem names_call (caller : Subst) (state : State) (names : List String) (argument answer : Atom)
    (captured : applySubst caller argument = namesValue names)
    (returned : PureReturns program (namesEnvironment names) state namesEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:names-patterns" [argument]) state answer := by
  apply PureData.raw_authored_call_return program caller (namesEnvironment names) state state
    "gslt:rule:names-patterns" [argument] namesEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · simp only [List.map_singleton, captured]
    exact names_clause names

private theorem names_cons_template :
    PureData.Template program (a "LCons" [a "FVar" [v "name"], v "tail"]) := by
  apply lcons_template _ (.captured _)
  apply PureData.Template.constructor "FVar" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .captured _

private theorem names_body_returns (state : State) (names : List String) :
    PureReturns program (namesEnvironment names) state namesEquation.body state
      (patternsValue (names.map Pattern.fvar)) := by
  induction names with
  | nil =>
      let caller := namesEnvironment []
      rw [names_shape]
      simp only [List.map_nil, patternsValue, encoded, InferenceCettaWire.encodePatterns, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "names") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ namesCases (read_cases_encoded _) _ _ _
      · simpa [caller, namesEnvironment, namesValue, namesTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "names"
      · simp [namesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons name names ih =>
      let caller := namesEnvironment (name :: names)
      let selected := ("rest", namesValue names) :: ("name", encoded (.string name)) :: caller
      let tailValue := patternsValue (names.map Pattern.fvar)
      let bound := ("tail", tailValue) :: selected
      have tailReturned := names_call selected state names (v "rest") tailValue
        (by simp [selected, caller, namesEnvironment, applySubst, Subst.lookup]) ih
      rw [names_shape]
      apply case_returns program caller selected state state state (v "names")
        (namesValue (name :: names)) namesConsBody _ _ namesCases (read_cases_encoded _) _ _ _
      · simpa [caller, namesEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "names"
      · simp [namesCases, namesTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, selected, caller, namesEnvironment, Subst.lookup]
      · apply let_returns program selected bound state state state (v "tail") _
          (a "LCons" [a "FVar" [v "name"], v "tail"]) tailValue _ tailReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, namesEnvironment]
        · simpa [List.map_cons, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, bound, tailValue, selected,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program bound state _ names_cons_template

/-- Variable-name preparation retains authored order and repeated names. -/
theorem names_patterns_captured_returns (caller : Subst) (state : State) (names : List String)
    (argument : Atom) (captured : applySubst caller argument = namesValue names) :
    PureReturns program caller state (a "gslt:rule:names-patterns" [argument]) state
      (patternsValue (names.map Pattern.fvar)) :=
  names_call caller state names argument _ captured (names_body_returns state names)

theorem names_patterns_returns (state : State) (names : List String) :
    PureReturns program [] state (a "gslt:rule:names-patterns" [namesValue names]) state
      (patternsValue (names.map Pattern.fvar)) :=
  names_patterns_captured_returns [] state names _ (by simp)

private def builtinEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:builtin-tuples")[0]'(by decide +kernel)

private def builtinEnvironment (relation : String) (arguments : List Pattern) : Subst :=
  [("arguments", patternsValue arguments), ("relation", encoded (.string relation))]

private def builtinTwoBody : Atom :=
  a "LCons" [a "LCons" [v "left", a "LCons" [v "left", .symbol "LNil"]],
    a "LCons" [a "LCons" [v "right", a "LCons" [v "right", .symbol "LNil"]], .symbol "LNil"]]

private def builtinCases : SpaceSemantics.Cases :=
  [(a "LCons" [v "left", a "LCons" [v "right", .symbol "LNil"]], builtinTwoBody),
   (v "bad", .symbol "LNil")]

private def builtinArguments : Atom :=
  a "case" [v "arguments", .expression (builtinCases.map fun row => .expression [row.1, row.2])]

private theorem builtin_shape : builtinEquation.body =
    a "if" [a "==" [v "relation", encoded (.string "eq")], builtinArguments, .symbol "LNil"] := by
  decide +kernel

private theorem builtin_clause (relation : String) (arguments : List Pattern) :
    clauses program "gslt:rule:builtin-tuples" [encoded (.string relation), patternsValue arguments] =
      [.evaluate (builtinEnvironment relation arguments) builtinEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:builtin-tuples").filterMap _ = _
  rw [show equations "gslt:rule:builtin-tuples" = [builtinEquation] from rfl]
  have formals : builtinEquation.arguments = [v "relation", v "arguments"] := by decide +kernel
  simp [formals, builtinEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem builtin_two_template : PureData.Template program builtinTwoBody := by
  unfold builtinTwoBody
  exact lcons_template
    (lcons_template (.captured _) (lcons_template (.captured _) (.symbol _)))
    (lcons_template
      (lcons_template (.captured _) (lcons_template (.captured _) (.symbol _))) (.symbol _))

private theorem builtin_fallback_returns (state : State) (relation : String) (arguments : List Pattern)
    (wrongArity : arguments.length ≠ 2) :
    PureReturns program (builtinEnvironment relation arguments) state builtinArguments state (.symbol "LNil") := by
  let caller := builtinEnvironment relation arguments
  let selected := ("bad", patternsValue arguments) :: caller
  apply case_returns program caller selected state state state (v "arguments")
    (patternsValue arguments) (.symbol "LNil") (.symbol "LNil") _ builtinCases (read_cases_encoded _) _ _ _
  · simpa [caller, builtinEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "arguments"
  · cases arguments with
    | nil =>
        simp [builtinCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup,
          caller, selected, builtinEnvironment]
    | cons left rest =>
        cases rest with
        | nil =>
            simp [builtinCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, caller, selected, builtinEnvironment]
        | cons right rest =>
            cases rest with
            | nil => exact False.elim (wrongArity rfl)
            | cons third rest =>
                simp [builtinCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, caller, selected, builtinEnvironment]
  · exact symbol_returns program selected state "LNil"

private theorem builtin_arguments_returns (state : State) (language : LanguageDef) (arguments : List Pattern) :
    PureReturns program (builtinEnvironment "eq" arguments) state builtinArguments state
      (tuplesValue (Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language "eq" arguments)) := by
  by_cases rightArity : arguments.length = 2
  · cases arguments with
    | nil => simp at rightArity
    | cons left rest =>
        cases rest with
        | nil => simp at rightArity
        | cons right rest =>
            have restEmpty : rest = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_cons] at rightArity
              omega
            subst rest
            let caller := builtinEnvironment "eq" [left, right]
            let selected := ("right", patternValue right) :: ("left", patternValue left) :: caller
            apply case_returns program caller selected state state state (v "arguments")
              (patternsValue [left, right]) builtinTwoBody _ _ builtinCases (read_cases_encoded _) _ _ _
            · simpa [caller, builtinEnvironment, applySubst, Subst.lookup] using
                variable_returns program caller state "arguments"
            · simp [builtinCases, InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, selected, caller, builtinEnvironment]
            · simpa [Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples, tuplesTerm, encodeList,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                builtinTwoBody, selected, caller, builtinEnvironment,
                applySubst, applySubst.applySubstList, Subst.lookup] using
                PureData.template_return program selected state _ builtin_two_template
  · have empty : Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language "eq" arguments = [] := by
      cases arguments with
      | nil => rfl
      | cons left rest =>
          cases rest with
          | nil => rfl
          | cons right rest =>
              cases rest with
              | nil => exact False.elim (rightArity rfl)
              | cons third rest => rfl
    simpa [empty, tuplesTerm, encodeList, CettaWireAtom.encode] using
      builtin_fallback_returns state "eq" arguments rightArity

private theorem builtin_body_returns (state : State) (language : LanguageDef)
    (relation : String) (arguments : List Pattern) :
    PureReturns program (builtinEnvironment relation arguments) state builtinEquation.body state
      (tuplesValue (Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation arguments)) := by
  let caller := builtinEnvironment relation arguments
  have tested := CettaWireAtom.equality_evaluated_returns program caller state
    (.string relation) (.string "eq") (v "relation") (encoded (.string "eq"))
    (by decide +kernel) (by decide +kernel)
    (by simpa [caller, builtinEnvironment, applySubst, Subst.lookup] using variable_returns program caller state "relation")
    (grounded_returns program caller state (.string "eq"))
  simp only [Term.string.injEq] at tested
  rw [builtin_shape]
  apply if_returns program caller state state state _ _ _ _ _ tested
  by_cases equality : relation = "eq"
  · subst relation
    simpa [Effects.boolean] using builtin_arguments_returns state language arguments
  · have empty : Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation arguments = [] := by
      simp [Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples, equality]
    simpa [empty, equality, Effects.boolean, tuplesTerm, encodeList, CettaWireAtom.encode] using
      symbol_returns program caller state "LNil"

/-- Only canonical binary equality supplies builtins; its two witness
occurrences remain distinct even when both tuples have identical payloads. -/
theorem builtin_tuples_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (relation : String) (arguments : List Pattern) (one two : Atom)
    (captured : [one, two].map (applySubst caller) = [encoded (.string relation), patternsValue arguments]) :
    PureReturns program caller state (a "gslt:rule:builtin-tuples" [one, two]) state
      (tuplesValue (Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation arguments)) := by
  apply PureData.raw_authored_call_return program caller (builtinEnvironment relation arguments) state state
    "gslt:rule:builtin-tuples" [one, two] builtinEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (builtin_body_returns state language relation arguments)
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [captured]
    exact builtin_clause relation arguments

theorem builtin_tuples_returns (state : State) (language : LanguageDef)
    (relation : String) (arguments : List Pattern) :
    PureReturns program [] state
      (a "gslt:rule:builtin-tuples" [encoded (.string relation), patternsValue arguments]) state
      (tuplesValue (Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language relation arguments)) :=
  builtin_tuples_captured_returns [] state language relation arguments _ _ (by simp)


private theorem tuples_as_list (tuples : List (List Pattern)) :
    tuplesValue tuples =
      MatchAutomataSourceExecution.listValue (tuples.map InferenceCettaWire.encodePatterns) := by
  simp only [tuplesValue, tuplesTerm, MatchAutomataSourceExecution.listValue,
    encodeList_map, Function.comp_def, id_eq]

private def queryEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:relation-query")[0]'(by decide +kernel)

private def queryEnvironment
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) : Subst :=
  [("seed", bindingsValue seed), ("rows", rowsValue rows),
   ("names", namesValue plan.arguments), ("relation", encoded (.string plan.relation))]

private def queryPairs : List (Atom × Atom) :=
  [(v "schemas", a "gslt:rule:names-patterns" [v "names"]),
   (v "arguments", a "gslt:rule:instantiate-children" [v "schemas", v "seed"]),
   (v "builtin", a "gslt:rule:builtin-tuples" [v "relation", v "arguments"]),
   (v "provided", a "gslt:rule:provider-tuples" [v "relation", v "rows"]),
   (v "tuples", a "gslt:automata:append" [v "builtin", v "provided"])]

private def queryResult : Atom :=
  a "gslt:rule:match-tuples" [v "names", v "tuples", v "seed"]

private theorem query_shape : queryEquation.body =
    a "let*" [.expression (queryPairs.map fun pair => .expression [pair.1, pair.2]), queryResult] := by
  decide +kernel

private theorem query_clause
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) :
    clauses program "gslt:rule:relation-query"
      [encoded (.string plan.relation), namesValue plan.arguments, rowsValue rows, bindingsValue seed] =
      [.evaluate (queryEnvironment rows plan seed) queryEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:relation-query").filterMap _ = _
  rw [show equations "gslt:rule:relation-query" = [queryEquation] from rfl]
  have formals : queryEquation.arguments = [v "relation", v "names", v "rows", v "seed"] := by
    decide +kernel
  simp [formals, queryEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem query_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) :
    PureReturns program (queryEnvironment rows plan seed) state queryEquation.body state
      (resultsValue (plan.run (providerEnv rows) language seed)) := by
  let caller := queryEnvironment rows plan seed
  let schemas := plan.arguments.map Pattern.fvar
  let arguments := schemas.map (applyBindings seed)
  let builtin := Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples language plan.relation arguments
  let provided := providerTuples rows plan.relation
  let tuples := builtin ++ provided
  let schemasBound := ("schemas", patternsValue schemas) :: caller
  let argumentsBound := ("arguments", patternsValue arguments) :: schemasBound
  let builtinBound := ("builtin", tuplesValue builtin) :: argumentsBound
  let providedBound := ("provided", tuplesValue provided) :: builtinBound
  let tuplesBound := ("tuples", tuplesValue tuples) :: providedBound
  have schemasReturned := names_patterns_captured_returns caller state plan.arguments (v "names")
    (by simp [caller, queryEnvironment, applySubst, Subst.lookup])
  have argumentsReturned : PureReturns program schemasBound state
      (a "gslt:rule:instantiate-children" [v "schemas", v "seed"]) state (patternsValue arguments) := by
    have erased : erasePatterns (plan.arguments.map PatternPlan.metavariable) = schemas := by
      simp [erasePatterns_eq_map, PatternPlan.erase, schemas]
    have instantiated : (plan.arguments.map PatternPlan.metavariable).map
        (PatternPlan.instantiate seed) = arguments := by
      rw [instantiateList_eq_applyBindings, erased]
    simpa only [instantiated] using RuleInstantiationExecution.instantiate_children_captured_returns
      schemasBound state seed (plan.arguments.map PatternPlan.metavariable)
      (v "schemas") (v "seed")
      (by simp [schemasBound, erased, caller, queryEnvironment, applySubst, Subst.lookup])
  have builtinReturned := builtin_tuples_captured_returns argumentsBound state language plan.relation
    arguments (v "relation") (v "arguments")
    (by simp [argumentsBound, schemasBound, caller, queryEnvironment, applySubst, Subst.lookup])
  have providedReturned := provider_tuples_captured_returns builtinBound state plan.relation rows
    (v "relation") (v "rows")
    (by simp [builtinBound, argumentsBound, schemasBound, caller, queryEnvironment, applySubst, Subst.lookup])
  have tuplesReturned : PureReturns program providedBound state
      (a "gslt:automata:append" [v "builtin", v "provided"]) state (tuplesValue tuples) := by
    apply automata_captured_returns (by decide +kernel)
    simpa only [tuples_as_list, List.map_append, tuples] using
      MatchAutomataSourceExecution.append_captured_returns providedBound state
        (builtin.map InferenceCettaWire.encodePatterns) (provided.map InferenceCettaWire.encodePatterns)
        (v "builtin") (v "provided")
        (by simp [providedBound, builtinBound, tuples_as_list, applySubst, Subst.lookup])
  have bindingsComputed : PureData.BindingsReturn program caller state queryPairs tuplesBound state := by
    apply PureData.BindingsReturn.cons (bound := schemasBound) schemasReturned
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, schemasBound, schemas, caller, queryEnvironment]
    apply PureData.BindingsReturn.cons (bound := argumentsBound) argumentsReturned
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, argumentsBound, schemasBound, caller, queryEnvironment]
    apply PureData.BindingsReturn.cons (bound := builtinBound) builtinReturned
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, builtinBound, builtin, argumentsBound, schemasBound, caller, queryEnvironment]
    apply PureData.BindingsReturn.cons (bound := providedBound) providedReturned
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, providedBound, provided, builtinBound, argumentsBound, schemasBound, caller, queryEnvironment]
    apply PureData.BindingsReturn.cons (bound := tuplesBound) tuplesReturned
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tuplesBound, providedBound, builtinBound, argumentsBound, schemasBound, caller, queryEnvironment]
    exact .nil _ _
  rw [query_shape]
  apply PureData.let_bindings_return bindingsComputed
  simpa only [PremisePlan.run, providerEnv, caller, schemas, arguments, builtin, provided, tuples, queryResult] using
    match_tuples_captured_returns tuplesBound state seed plan tuples
      (v "names") (v "tuples") (v "seed")
      (by simp [tuplesBound, providedBound, builtinBound, argumentsBound, schemasBound,
        caller, queryEnvironment, applySubst, Subst.lookup])

/-- The retained query prepares its schemas and substituted arguments, gathers
canonical builtin and provider occurrences, then performs canonical literal
matching. All intermediate lists and binding order come from actual execution. -/
theorem relation_query_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) (one two three four : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded (.string plan.relation), namesValue plan.arguments, rowsValue rows, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:relation-query" [one, two, three, four]) state
      (resultsValue (plan.run (providerEnv rows) language seed)) := by
  apply PureData.raw_authored_call_return program caller (queryEnvironment rows plan seed) state state
    "gslt:rule:relation-query" [one, two, three, four] queryEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _
    (query_body_returns state language rows plan seed)
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact query_clause rows plan seed

def relationQueryTerm
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) : Term :=
  .application "gslt:rule:relation-query"
    [.string plan.relation, namesTerm plan.arguments, providerRowsTerm rows, bindingsTerm seed]

theorem relation_query_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) :
    PureReturns program [] state (encoded (relationQueryTerm rows plan seed)) state
      (resultsValue (plan.run (providerEnv rows) language seed)) :=
  relation_query_captured_returns [] state language rows plan seed _ _ _ _ (by simp)

theorem relation_query_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (encoded (relationQueryTerm rows plan seed)) } =
        .complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (plan.run (providerEnv rows) language seed)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (relation_query_returns state language rows plan seed) after answers input output

theorem relation_query_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plan : PremisePlan) (seed : Bindings) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (relationQueryTerm rows plan seed)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (plan.run (providerEnv rows) language seed)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (relation_query_returns state language rows plan seed) after answers input output

/-! ## Canonical ordered premise folds -/

/-- The existing relation-premise wire retains its variable schemas; query
preparation performs substitution after those schemas are read. -/
def premiseTerm (plan : PremisePlan) : Term :=
  .application "RelationQuery" [.string plan.relation,
    InferenceCettaWire.encodePatterns (plan.arguments.map Pattern.fvar)]

/-- Every authored premise occurrence is retained in order. -/
def premisesTerm (plans : List PremisePlan) : Term := encodeList premiseTerm plans

private abbrev premisesValue (plans : List PremisePlan) : Atom := encoded (premisesTerm plans)

private def argumentNamesEquation : SpaceSemantics.Equation :=
  (equations "gslt:rule:argument-names")[0]'(by decide +kernel)

private def argumentNamesEnvironment (names : List String) : Subst :=
  [("arguments", patternsValue (names.map Pattern.fvar))]

private def argumentNamesCons : Atom :=
  a "let" [v "tail", a "gslt:rule:argument-names" [v "rest"], a "LCons" [v "name", v "tail"]]

private def argumentNamesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [a "FVar" [v "name"], v "rest"], argumentNamesCons)]

private theorem argumentNames_shape : argumentNamesEquation.body =
    a "case" [v "arguments", .expression (argumentNamesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem argumentNames_clause (names : List String) :
    clauses program "gslt:rule:argument-names" [patternsValue (names.map Pattern.fvar)] =
      [.evaluate (argumentNamesEnvironment names) argumentNamesEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:rule:argument-names").filterMap _ = _
  rw [show equations "gslt:rule:argument-names" = [argumentNamesEquation] from rfl]
  have formals : argumentNamesEquation.arguments = [v "arguments"] := by decide +kernel
  simp [formals, argumentNamesEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem argumentNames_call (caller : Subst) (state : State) (names : List String) (argument answer : Atom)
    (captured : applySubst caller argument = patternsValue (names.map Pattern.fvar))
    (returned : PureReturns program (argumentNamesEnvironment names) state argumentNamesEquation.body state answer) :
    PureReturns program caller state (a "gslt:rule:argument-names" [argument]) state answer := by
  apply PureData.raw_authored_call_return program caller (argumentNamesEnvironment names) state state
    "gslt:rule:argument-names" [argument] argumentNamesEquation.body answer
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ returned
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · simp only [List.map_singleton, captured]
    exact argumentNames_clause names

private theorem argumentNames_body_returns (state : State) (names : List String) :
    PureReturns program (argumentNamesEnvironment names) state argumentNamesEquation.body state (namesValue names) := by
  induction names with
  | nil =>
      let caller := argumentNamesEnvironment []
      rw [argumentNames_shape]
      simp only [namesValue, namesTerm, encoded, encodeList, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "arguments") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ argumentNamesCases (read_cases_encoded _) _ _ _
      · simpa [caller, argumentNamesEnvironment, List.map_nil, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "arguments"
      · simp [argumentNamesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons name names ih =>
      let caller := argumentNamesEnvironment (name :: names)
      let selected := ("rest", patternsValue (names.map Pattern.fvar)) :: ("name", encoded (.string name)) :: caller
      let bound := ("tail", namesValue names) :: selected
      have tailReturned := argumentNames_call selected state names (v "rest") (namesValue names)
        (by simp [selected, caller, argumentNamesEnvironment, applySubst, Subst.lookup]) ih
      rw [argumentNames_shape]
      apply case_returns program caller selected state state state (v "arguments")
        (patternsValue ((name :: names).map Pattern.fvar)) argumentNamesCons _ _
        argumentNamesCases (read_cases_encoded _) _ _ _
      · simpa [caller, argumentNamesEnvironment, applySubst, Subst.lookup] using
          variable_returns program caller state "arguments"
      · simp [argumentNamesCases, List.map_cons, InferenceCettaWire.encodePatterns, InferenceCettaWire.encodePattern,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          selected, caller, argumentNamesEnvironment, Subst.lookup]
      · apply let_returns program selected bound state state state (v "tail") _
          (a "LCons" [v "name", v "tail"]) (namesValue names) _ tailReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, caller, argumentNamesEnvironment]
        · convert PureData.template_return program bound state
            (a "LCons" [v "name", v "tail"]) (lcons_template (.captured _) (.captured _)) using 1
          rfl

/-- Canonical variable schemas have an exact inverse name projection. Other
pattern forms are outside this admitted source operation. -/
theorem argument_names_captured_returns (caller : Subst) (state : State) (names : List String)
    (argument : Atom) (captured : applySubst caller argument = patternsValue (names.map Pattern.fvar)) :
    PureReturns program caller state (a "gslt:rule:argument-names" [argument]) state (namesValue names) :=
  argumentNames_call caller state names argument _ captured (argumentNames_body_returns state names)

theorem argument_names_returns (state : State) (names : List String) :
    PureReturns program [] state
      (a "gslt:rule:argument-names" [patternsValue (names.map Pattern.fvar)]) state (namesValue names) :=
  argument_names_captured_returns [] state names _ (by simp)

private inductive FoldHelper where | premises | results
private def FoldHelper.head : FoldHelper → String
  | .premises => "gslt:rule:premises"
  | .results => "gslt:rule:premise-results"
private def FoldHelper.last : FoldHelper → String
  | .premises => "seed"
  | .results => "results"
private def foldEquation (helper : FoldHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def foldEnvironment (helper : FoldHelper) (plans : List PremisePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (last : Atom) : Subst :=
  [(helper.last, last), ("rows", rowsValue rows), ("premises", premisesValue plans)]

private theorem fold_clause (helper : FoldHelper) (plans : List PremisePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (last : Atom) :
    clauses program helper.head [premisesValue plans, rowsValue rows, last] =
      [.evaluate (foldEnvironment helper plans rows last) (foldEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  rw [show equations helper.head = [foldEquation helper] from by cases helper <;> rfl]
  have formals : (foldEquation helper).arguments = [v "premises", v "rows", v helper.last] := by
    cases helper <;> decide +kernel
  cases helper <;> simp [formals, foldEnvironment, FoldHelper.last,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem fold_call (helper : FoldHelper) (caller : Subst) (state : State) (plans : List PremisePlan)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (last one two three answer : Atom)
    (captured : [one, two, three].map (applySubst caller) = [premisesValue plans, rowsValue rows, last])
    (returned : PureReturns program (foldEnvironment helper plans rows last) state
      (foldEquation helper).body state answer) :
    PureReturns program caller state (a helper.head [one, two, three]) state answer := by
  apply PureData.raw_authored_call_return program caller (foldEnvironment helper plans rows last) state state
    helper.head [one, two, three] (foldEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact fold_clause helper plans rows last

private def premisesConsPairs : List (Atom × Atom) :=
  [(v "names", a "gslt:rule:argument-names" [v "arguments"]),
   (v "choices", a "gslt:rule:relation-query" [v "relation", v "names", v "rows", v "seed"])]
private def premisesConsResult : Atom :=
  a "gslt:rule:premise-results" [v "rest", v "rows", v "choices"]
private def premisesConsBody : Atom :=
  a "let*" [.expression (premisesConsPairs.map fun pair => .expression [pair.1, pair.2]), premisesConsResult]
private def premisesCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "LCons" [v "seed", .symbol "LNil"]),
   (a "LCons" [a "RelationQuery" [v "relation", v "arguments"], v "rest"], premisesConsBody)]

private def foldResultsConsPairs : List (Atom × Atom) :=
  [(v "head", a "gslt:rule:premises" [v "premises", v "rows", v "seed"]),
   (v "tail", a "gslt:rule:premise-results" [v "premises", v "rows", v "rest"])]
private def foldResultsConsResult : Atom := a "gslt:automata:append" [v "head", v "tail"]
private def foldResultsConsBody : Atom :=
  a "let*" [.expression (foldResultsConsPairs.map fun pair => .expression [pair.1, pair.2]), foldResultsConsResult]
private def foldResultsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "seed", v "rest"], foldResultsConsBody)]

private theorem premises_shape : (foldEquation .premises).body =
    a "case" [v "premises", .expression (premisesCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel
private theorem foldResults_shape : (foldEquation .results).body =
    a "case" [v "results", .expression (foldResultsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem results_as_list (results : List Bindings) :
    resultsValue results = MatchAutomataSourceExecution.listValue (results.map bindingsTerm) := by
  simp only [resultsValue, bindingResultsTerm, MatchAutomataSourceExecution.listValue,
    encodeList_map, Function.comp_def, id_eq]

private theorem result_append_captured_returns (caller : Subst) (state : State) (left right : List Bindings)
    (captured : [v "head", v "tail"].map (applySubst caller) = [resultsValue left, resultsValue right]) :
    PureReturns program caller state foldResultsConsResult state (resultsValue (left ++ right)) := by
  apply automata_captured_returns (by decide +kernel)
  simpa only [foldResultsConsResult, a, v, results_as_list, List.map_append] using
    MatchAutomataSourceExecution.append_captured_returns caller state
      (left.map bindingsTerm) (right.map bindingsTerm) (v "head") (v "tail")
      (by simpa only [results_as_list] using captured)

private theorem foldResults_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (allSeeds : ∀ seed : Bindings,
      PureReturns program (foldEnvironment .premises plans rows (bindingsValue seed)) state
        (foldEquation .premises).body state (resultsValue (runPremisePlans (providerEnv rows) language plans seed)))
    (results : List Bindings) :
    PureReturns program (foldEnvironment .results plans rows (resultsValue results)) state
      (foldEquation .results).body state
      (resultsValue (results.flatMap (runPremisePlans (providerEnv rows) language plans))) := by
  induction results with
  | nil =>
      let caller := foldEnvironment .results plans rows (resultsValue [])
      rw [foldResults_shape]
      simp only [List.flatMap_nil, resultsValue, encoded, bindingResultsTerm, encodeList, CettaWireAtom.encode]
      apply case_returns program caller caller state state state (v "results") (.symbol "LNil")
        (.symbol "LNil") (.symbol "LNil") _ foldResultsCases (read_cases_encoded _) _ _ _
      · simpa [caller, foldEnvironment, FoldHelper.last, bindingResultsTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using
          variable_returns program caller state "results"
      · simp [foldResultsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons seed results ih =>
      let caller := foldEnvironment .results plans rows (resultsValue (seed :: results))
      let selected := ("rest", resultsValue results) :: ("seed", bindingsValue seed) :: caller
      let headValue := resultsValue (runPremisePlans (providerEnv rows) language plans seed)
      let headBound := ("head", headValue) :: selected
      let tailValue := resultsValue (results.flatMap (runPremisePlans (providerEnv rows) language plans))
      let tailBound := ("tail", tailValue) :: headBound
      have headReturned := fold_call .premises selected state plans rows (bindingsValue seed)
        (v "premises") (v "rows") (v "seed") headValue
        (by simp [selected, caller, foldEnvironment, FoldHelper.last, applySubst, Subst.lookup]) (allSeeds seed)
      have tailReturned := fold_call .results headBound state plans rows (resultsValue results)
        (v "premises") (v "rows") (v "rest") tailValue
        (by simp [headBound, selected, caller, foldEnvironment, FoldHelper.last, applySubst, Subst.lookup]) ih
      rw [foldResults_shape]
      apply case_returns program caller selected state state state (v "results") (resultsValue (seed :: results))
        foldResultsConsBody _ _ foldResultsCases (read_cases_encoded _) _ _ _
      · simpa [caller, foldEnvironment, FoldHelper.last, applySubst, Subst.lookup] using
          variable_returns program caller state "results"
      · simp [foldResultsCases, bindingResultsTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, selected, caller, foldEnvironment, FoldHelper.last]
      · have computed : PureData.BindingsReturn program selected state foldResultsConsPairs tailBound state := by
          apply PureData.BindingsReturn.cons (bound := headBound) headReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound, selected,
              caller, foldEnvironment, FoldHelper.last]
          apply PureData.BindingsReturn.cons (bound := tailBound) tailReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, headBound, selected,
              caller, foldEnvironment, FoldHelper.last]
          exact .nil _ _
        have appended := result_append_captured_returns tailBound state
          (runPremisePlans (providerEnv rows) language plans seed)
          (results.flatMap (runPremisePlans (providerEnv rows) language plans))
          (by simp [tailBound, tailValue, headBound, headValue, applySubst, Subst.lookup])
        simpa only [foldResultsConsBody, List.flatMap_cons] using
          PureData.let_bindings_return computed state foldResultsConsResult _ appended

private theorem premises_body_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan) :
    ∀ seed : Bindings,
      PureReturns program (foldEnvironment .premises plans rows (bindingsValue seed)) state
        (foldEquation .premises).body state
        (resultsValue (runPremisePlans (providerEnv rows) language plans seed)) := by
  induction plans with
  | nil =>
      intro seed
      let caller := foldEnvironment .premises [] rows (bindingsValue seed)
      rw [premises_shape]
      apply case_returns program caller caller state state state (v "premises") (.symbol "LNil")
        (a "LCons" [v "seed", .symbol "LNil"]) _ _ premisesCases (read_cases_encoded _) _ _ _
      · simpa [caller, foldEnvironment, FoldHelper.last, premisesValue, premisesTerm, encodeList,
          CettaWireAtom.encode, applySubst, Subst.lookup] using variable_returns program caller state "premises"
      · simp [premisesCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · convert PureData.template_return program caller state
          (a "LCons" [v "seed", .symbol "LNil"]) (lcons_template (.captured _) (.symbol _)) using 1
        rfl
  | cons plan plans ih =>
      intro seed
      let caller := foldEnvironment .premises (plan :: plans) rows (bindingsValue seed)
      let selected := ("rest", premisesValue plans) :: ("arguments", patternsValue (plan.arguments.map Pattern.fvar)) ::
        ("relation", encoded (.string plan.relation)) :: caller
      let namesBound := ("names", namesValue plan.arguments) :: selected
      let choices := plan.run (providerEnv rows) language seed
      let choicesBound := ("choices", resultsValue choices) :: namesBound
      have namesReturned := argument_names_captured_returns selected state plan.arguments (v "arguments")
        (by simp [selected, caller, foldEnvironment, applySubst, Subst.lookup])
      have choicesReturned := relation_query_captured_returns namesBound state language rows plan seed
        (v "relation") (v "names") (v "rows") (v "seed")
        (by simp [namesBound, selected, caller, foldEnvironment, FoldHelper.last, applySubst, Subst.lookup])
      have continued := fold_call .results choicesBound state plans rows (resultsValue choices)
        (v "rest") (v "rows") (v "choices")
        (resultsValue (choices.flatMap (runPremisePlans (providerEnv rows) language plans)))
        (by simp [choicesBound, namesBound, selected, caller, foldEnvironment, FoldHelper.last,
          applySubst, Subst.lookup])
        (foldResults_body_returns state language rows plans ih choices)
      rw [premises_shape]
      apply case_returns program caller selected state state state (v "premises")
        (premisesValue (plan :: plans)) premisesConsBody _ _ premisesCases (read_cases_encoded _) _ _ _
      · simpa [caller, foldEnvironment, FoldHelper.last, applySubst, Subst.lookup] using
          variable_returns program caller state "premises"
      · simp [premisesCases, premisesValue, premisesTerm, premiseTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, caller, foldEnvironment, FoldHelper.last]
      · have computed : PureData.BindingsReturn program selected state premisesConsPairs choicesBound state := by
          apply PureData.BindingsReturn.cons (bound := namesBound) namesReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, namesBound, selected,
              caller, foldEnvironment, FoldHelper.last]
          apply PureData.BindingsReturn.cons (bound := choicesBound) choicesReturned
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, choicesBound, choices, namesBound,
              selected, caller, foldEnvironment, FoldHelper.last]
          exact .nil _ _
        simpa only [premisesConsBody, runPremisePlans, choices] using
          PureData.let_bindings_return computed state premisesConsResult _ continued

/-- The retained premise fold realizes the existing ordered interpreter for
every seed, including branching and duplicate successful tuple occurrences. -/
theorem premises_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (seed : Bindings) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [premisesValue plans, rowsValue rows, bindingsValue seed]) :
    PureReturns program caller state (a "gslt:rule:premises" [one, two, three]) state
      (resultsValue (runPremisePlans (providerEnv rows) language plans seed)) :=
  fold_call .premises caller state plans rows (bindingsValue seed) one two three _ captured
    (premises_body_returns state language rows plans seed)

def premisesQueryTerm (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List PremisePlan) (seed : Bindings) : Term :=
  .application "gslt:rule:premises" [premisesTerm plans, providerRowsTerm rows, bindingsTerm seed]

theorem premises_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan) (seed : Bindings) :
    PureReturns program [] state (encoded (premisesQueryTerm rows plans seed)) state
      (resultsValue (runPremisePlans (providerEnv rows) language plans seed)) :=
  premises_captured_returns [] state language rows plans seed _ _ _ (by simp)

/-- Each incoming choice continues the same authored premise suffix; append
retains choice order and all duplicate binding observations. -/
theorem premise_results_captured_returns (caller : Subst) (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (results : List Bindings) (one two three : Atom)
    (captured : [one, two, three].map (applySubst caller) =
      [premisesValue plans, rowsValue rows, resultsValue results]) :
    PureReturns program caller state (a "gslt:rule:premise-results" [one, two, three]) state
      (resultsValue (results.flatMap (runPremisePlans (providerEnv rows) language plans))) :=
  fold_call .results caller state plans rows (resultsValue results) one two three _ captured
    (foldResults_body_returns state language rows plans (premises_body_returns state language rows plans) results)

def premiseResultsQueryTerm (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
    (plans : List PremisePlan) (results : List Bindings) : Term :=
  .application "gslt:rule:premise-results" [premisesTerm plans, providerRowsTerm rows, bindingResultsTerm results]

theorem premise_results_returns (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (results : List Bindings) :
    PureReturns program [] state (encoded (premiseResultsQueryTerm rows plans results)) state
      (resultsValue (results.flatMap (runPremisePlans (providerEnv rows) language plans))) :=
  premise_results_captured_returns [] state language rows plans results _ _ _ (by simp)

theorem premises_completed_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan) (seed : Bindings)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (encoded (premisesQueryTerm rows plans seed)) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (runPremisePlans (providerEnv rows) language plans seed)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (premises_returns state language rows plans seed)
    after answers input output

theorem premises_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan) (seed : Bindings)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (premisesQueryTerm rows plans seed)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (runPremisePlans (providerEnv rows) language plans seed)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (premises_returns state language rows plans seed)
    after answers input output

theorem premise_results_derivation_iff (state : State) (language : LanguageDef)
    (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow) (plans : List PremisePlan)
    (results : List Bindings) (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (encoded (premiseResultsQueryTerm rows plans results)) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [resultsValue (results.flatMap (runPremisePlans (providerEnv rows) language plans))] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (premise_results_returns state language rows plans results)
    after answers input output

namespace Controls

/-- Test inputs select retained tuple and preparation operations without
defining another premise interpreter. Expected values use the shared matcher
and canonical builtin relation tuples. -/
inductive Input where
  | argument (name : String) (value : Pattern)
  | arguments (names : List String) (values : List Pattern)
  | tuple (plan : PremisePlan) (values : List Pattern)
  | tuples (plan : PremisePlan) (values : List (List Pattern))
  | names (values : List String)
  | builtin (relation : String) (arguments : List Pattern)
  | argumentNames (names : List String)
  | provider (relation : String) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
  | query (plan : PremisePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
  | premises (plans : List PremisePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
  | results (plans : List PremisePlan) (rows : List Mettapedia.OSLF.MeTTaIL.GeneralPremise.ProviderRow)
      (choices : List Bindings)

structure Fixture where
  name : String
  input : Input
  seed : Bindings

def fixtures : List Fixture :=
  [⟨"argument-introduces-relative-binding", .argument "x" (.apply "a" []), []⟩,
   ⟨"argument-already-bound-yields-empty-extension", .argument "x" (.apply "a" []), [("x", .apply "a" [])]⟩,
   ⟨"argument-conflict", .argument "x" (.apply "b" []), [("x", .apply "a" [])]⟩,
   ⟨"bound-value-is-literal-variable-data", .argument "x" (.fvar "inner"),
     [("x", .fvar "inner"), ("inner", .apply "resolved" [])]⟩,
   ⟨"relative-extension-order", .arguments ["x", "y"] [.apply "a" [], .apply "b" []],
     [("z", .apply "c" [])]⟩,
   ⟨"nullary-relative-extension", .arguments [] [], [("z", .apply "c" [])]⟩,
   ⟨"relative-arity-too-many-values", .arguments [] [.apply "a" []], []⟩,
   ⟨"relative-arity-too-few-values", .arguments ["x"] [], []⟩,
   ⟨"repeated-variable-consistent", .tuple ⟨"r", ["x", "x"]⟩ [.apply "a" [], .apply "a" []], []⟩,
   ⟨"repeated-variable-conflict", .tuple ⟨"r", ["x", "x"]⟩ [.apply "a" [], .apply "b" []], []⟩,
   ⟨"complete-seed-merge-order", .tuple ⟨"r", ["x", "y"]⟩ [.apply "a" [], .apply "b" []],
     [("z", .apply "c" [])]⟩,
   ⟨"nullary-tuple-retains-original-seed", .tuple ⟨"r", []⟩ [], [("z", .apply "c" [])]⟩,
   ⟨"tuple-arity-refusal", .tuple ⟨"r", ["x", "y"]⟩ [.apply "a" []], []⟩,
   ⟨"ordered-duplicate-tuples", .tuples ⟨"r", ["x"]⟩
     [[.apply "a" []], [.apply "a" []], [.apply "b" []]], []⟩,
   ⟨"mixed-refused-and-accepted-tuples", .tuples ⟨"r", ["x", "x"]⟩
     [[.apply "a" [], .apply "b" []], [.apply "a" [], .apply "a" []], [], [.apply "b" [], .apply "b" []]], []⟩,
   ⟨"empty-provider-row", .tuples ⟨"r", ["x"]⟩ [], []⟩,
   ⟨"opaque-prebound-variable-payload", .tuples ⟨"r", ["x"]⟩
     [[.fvar "inner"], [.apply "resolved" []]],
     [("x", .fvar "inner"), ("inner", .apply "resolved" [])]⟩,
   ⟨"original-seed-entries-retained", .tuples ⟨"r", ["x"]⟩ [[.apply "a" []], [.apply "b" []]],
     [("x", .apply "a" []), ("x", .apply "b" [])]⟩,
   ⟨"binder-containing-tuple-payload", .tuple ⟨"r", ["x"]⟩ [.lambda "bound" (.bvar 0)], []⟩]

/-- Preparation controls are separate so the original tuple corpus remains
byte-for-byte reproducible when later helper packages are added. -/
def preparationFixtures : List Fixture :=
  [⟨"names-empty", .names [], []⟩,
   ⟨"names-retain-order-and-repetition", .names ["y", "x", "y"], []⟩,
   ⟨"names-retain-quoted-spelling", .names ["a/b", "$x", "eq"], []⟩,
   ⟨"builtin-two-different-witnesses", .builtin "eq" [.apply "a" [], .apply "b" []], []⟩,
   ⟨"builtin-two-duplicate-witnesses", .builtin "eq" [.apply "a" [], .apply "a" []], []⟩,
   ⟨"builtin-opaque-variable-and-binder-payloads",
     .builtin "eq" [.fvar "inner", .lambda "bound" (.bvar 0)], []⟩,
   ⟨"builtin-zero-arity", .builtin "eq" [], []⟩,
   ⟨"builtin-missing-argument", .builtin "eq" [.apply "a" []], []⟩,
   ⟨"builtin-extra-argument", .builtin "eq" [.apply "a" [], .apply "b" [], .apply "c" []], []⟩,
   ⟨"builtin-different-relation", .builtin "EQ" [.apply "a" [], .apply "b" []], []⟩]

/-- These controls share the independent query and ordered-fold functions with
the source execution laws. Earlier tuple and preparation controls are retained. -/
def premiseFixtures : List Fixture :=
  [⟨"argument-names-empty", .argumentNames [], []⟩,
   ⟨"argument-names-order-and-repetition", .argumentNames ["y", "x", "y"], []⟩,
   ⟨"provider-retains-row-order-and-duplicates", .provider "r"
     [⟨"r", [.apply "a" []]⟩, ⟨"other", [.apply "c" []]⟩,
      ⟨"r", [.apply "a" []]⟩, ⟨"r", [.apply "b" []]⟩], []⟩,
   ⟨"provider-missing-relation", .provider "s" [⟨"r", [.apply "a" []]⟩], []⟩,
   ⟨"provider-nullary-duplicate-rows", .provider "r" [⟨"r", []⟩, ⟨"r", []⟩], []⟩,
   ⟨"query-ordered-duplicate-provider-witnesses", .query ⟨"r", ["x"]⟩
     [⟨"r", [.apply "a" []]⟩, ⟨"r", [.apply "a" []]⟩, ⟨"r", [.apply "b" []]⟩], []⟩,
   ⟨"query-duplicate-equality-witnesses", .query ⟨"eq", ["x", "x"]⟩ [], []⟩,
   ⟨"query-conflicting-prebound-equality", .query ⟨"eq", ["x", "y"]⟩ [],
     [("x", .apply "a" []), ("y", .apply "b" [])]⟩,
   ⟨"query-builtin-before-provider-witnesses", .query ⟨"eq", ["x", "y"]⟩
     [⟨"eq", [.apply "c" [], .apply "c" []]⟩], []⟩,
   ⟨"query-prebound-variable-remains-literal", .query ⟨"r", ["x"]⟩
     [⟨"r", [.fvar "inner"]⟩, ⟨"r", [.apply "resolved" []]⟩],
     [("x", .fvar "inner"), ("inner", .apply "resolved" [])]⟩,
   ⟨"query-repeated-variable-refusals", .query ⟨"r", ["x", "x"]⟩
     [⟨"r", [.apply "a" [], .apply "b" []]⟩, ⟨"r", [.apply "a" [], .apply "a" []]⟩,
      ⟨"r", []⟩], []⟩,
   ⟨"premises-empty-retains-seed-order", .premises [] [],
     [("y", .apply "b" []), ("x", .apply "a" []), ("x", .apply "c" [])]⟩,
   ⟨"premises-ordered-branching-duplicates", .premises [⟨"r", ["x"]⟩, ⟨"s", ["x", "y"]⟩]
     [⟨"r", [.apply "a" []]⟩, ⟨"s", [.apply "a" [], .apply "u" []]⟩,
      ⟨"r", [.apply "a" []]⟩, ⟨"s", [.apply "a" [], .apply "v" []]⟩,
      ⟨"r", [.apply "b" []]⟩, ⟨"s", [.apply "b" [], .apply "w" []]⟩], []⟩,
   ⟨"premises-second-query-conflict", .premises [⟨"r", ["x"]⟩, ⟨"s", ["x"]⟩]
     [⟨"r", [.apply "a" []]⟩, ⟨"s", [.apply "b" []]⟩], []⟩,
   ⟨"premises-missing-first-query", .premises [⟨"r", ["x"]⟩, ⟨"s", ["y"]⟩]
     [⟨"s", [.apply "a" []]⟩], []⟩,
   ⟨"premises-nullary-duplicate-branches", .premises [⟨"r", []⟩]
     [⟨"r", []⟩, ⟨"r", []⟩], [("z", .apply "c" [])]⟩,
   ⟨"premise-results-empty-choice-list", .results [⟨"r", ["x"]⟩]
     [⟨"r", [.apply "a" []]⟩] [], []⟩,
   ⟨"premise-results-retains-duplicate-incoming-choices", .results [] []
     [[("x", .apply "a" [])], [("x", .apply "a" [])], [("x", .apply "b" [])]], []⟩,
   ⟨"premise-results-refuses-conflicting-choices", .results [⟨"r", ["x"]⟩]
     [⟨"r", [.apply "a" []]⟩] [[("x", .apply "b" [])], [("x", .apply "a" [])]], []⟩]

def Fixture.queryTerm (fixture : Fixture) : Term :=
  let seed := bindingsTerm fixture.seed
  match fixture.input with
  | .argument name value => .application "gslt:rule:relation-argument"
      [.string name, InferenceCettaWire.encodePattern value, seed]
  | .arguments names values => .application "gslt:rule:relation-arguments"
      [namesTerm names, InferenceCettaWire.encodePatterns values, seed]
  | .tuple plan values => .application "gslt:rule:match-tuple"
      [namesTerm plan.arguments, InferenceCettaWire.encodePatterns values, seed]
  | .tuples plan values => .application "gslt:rule:match-tuples"
      [namesTerm plan.arguments, tuplesTerm values, seed]
  | .names values => .application "gslt:rule:names-patterns" [namesTerm values]
  | .builtin relation arguments => .application "gslt:rule:builtin-tuples"
      [.string relation, InferenceCettaWire.encodePatterns arguments]
  | .argumentNames names => .application "gslt:rule:argument-names"
      [InferenceCettaWire.encodePatterns (names.map Pattern.fvar)]
  | .provider relation rows => .application "gslt:rule:provider-tuples" [.string relation, providerRowsTerm rows]
  | .query plan rows => relationQueryTerm rows plan fixture.seed
  | .premises plans rows => premisesQueryTerm rows plans fixture.seed
  | .results plans rows choices => premiseResultsQueryTerm rows plans choices

def Fixture.expectedTerm (fixture : Fixture) : Term :=
  match fixture.input with
  | .argument name value => bindingsOptionTerm (relationArgument? fixture.seed name value)
  | .arguments names values => bindingsOptionTerm (relationArguments? fixture.seed names values)
  | .tuple plan values => bindingsOptionTerm (plan.matchTuple? fixture.seed values)
  | .tuples plan values => bindingResultsTerm (values.filterMap (plan.matchTuple? fixture.seed))
  | .names values => InferenceCettaWire.encodePatterns (values.map Pattern.fvar)
  | .builtin relation arguments => tuplesTerm
      (Mettapedia.OSLF.MeTTaIL.Engine.builtinRelationTuples (LanguageDef.empty fixture.name) relation arguments)
  | .argumentNames names => namesTerm names
  | .provider relation rows => tuplesTerm (providerTuples rows relation)
  | .query plan rows => bindingResultsTerm (plan.run (providerEnv rows) (LanguageDef.empty fixture.name) fixture.seed)
  | .premises plans rows => bindingResultsTerm
      (runPremisePlans (providerEnv rows) (LanguageDef.empty fixture.name) plans fixture.seed)
  | .results plans rows choices => bindingResultsTerm
      (choices.flatMap (runPremisePlans (providerEnv rows) (LanguageDef.empty fixture.name) plans))

theorem Fixture.returns (fixture : Fixture) (state : State) :
    PureReturns program [] state (CettaWireAtom.encode fixture.queryTerm) state
      (CettaWireAtom.encode fixture.expectedTerm) := by
  rcases fixture with ⟨name, input, seed⟩
  cases input with
  | argument key value =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        relation_argument_returns state seed key value
  | arguments names values =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        relation_arguments_returns state seed names values
  | tuple plan values =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        match_tuple_returns state seed plan values
  | tuples plan values =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        match_tuples_returns state seed plan values
  | names values =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        names_patterns_returns state values
  | builtin relation arguments =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        builtin_tuples_returns state (LanguageDef.empty name) relation arguments
  | argumentNames names =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        argument_names_returns state names
  | provider relation rows =>
      simpa [Fixture.queryTerm, Fixture.expectedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        provider_tuples_returns state relation rows
  | query plan rows =>
      exact relation_query_returns state (LanguageDef.empty name) rows plan seed
  | premises plans rows =>
      exact premises_returns state (LanguageDef.empty name) rows plans seed
  | results plans rows choices =>
      exact premise_results_returns state (LanguageDef.empty name) rows plans choices

end Controls

#print axioms relation_argument_returns
#print axioms relation_arguments_returns
#print axioms match_tuple_returns
#print axioms match_tuples_returns
#print axioms match_tuples_canonical_returns
#print axioms match_tuples_derivation_iff
#print axioms names_patterns_returns
#print axioms builtin_tuples_returns
#print axioms provider_tuples_returns
#print axioms relation_query_returns
#print axioms relation_query_completed_iff
#print axioms relation_query_derivation_iff
#print axioms argument_names_returns
#print axioms premises_returns
#print axioms premise_results_returns
#print axioms premises_completed_iff
#print axioms premises_derivation_iff
#print axioms premise_results_derivation_iff
#print axioms Controls.Fixture.returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RelationPremiseExecution
