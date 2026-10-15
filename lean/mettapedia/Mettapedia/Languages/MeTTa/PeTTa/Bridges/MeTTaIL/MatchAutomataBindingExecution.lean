import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataSourceExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataDerivativeExecution
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata

/-!
# Canonical bindings through the retained PeTTa matching program

The structural automata share one binding continuation. These laws execute
its retained equations against the independent MeTTaIL matcher. Binding order
and repeated-variable checks are retained, including for captured values whose
payloads resemble executable calls. Every computation preserves its supplied
store and produces no input or output observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataDerivativeExecution (positionTerm locationTerm)
open SubtermMatching (Location Position)
open MeTTaILSubtermMatchAutomata (BoundMatch subterms subtermsList)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

def bindingTerm (binding : String × Pattern) : Term :=
  .application "Binding" [.string binding.1, InferenceCettaWire.encodePattern binding.2]

def bindingsTerm (bindings : Bindings) : Term := encodeList bindingTerm bindings

/-- A binding's wire representation retains both its variable name and its
complete canonical pattern. -/
theorem bindingTerm_injective : Function.Injective bindingTerm := by
  intro left right same
  have arguments := (Term.application.inj same).2
  have names := Term.string.inj (List.cons.inj arguments).1
  have patterns := InferenceCettaWire.encodePattern_injective
    (List.cons.inj (List.cons.inj arguments).2).1
  exact Prod.ext names patterns

/-- Binding order and duplicate entries remain distinguishable on the wire. -/
theorem bindingsTerm_injective : Function.Injective bindingsTerm :=
  encodeList_injective bindingTerm bindingTerm_injective

def patternOptionTerm : Option Pattern → Term
  | none => .symbol "None"
  | some value => .application "Some" [InferenceCettaWire.encodePattern value]

/-- The option wire distinguishes failure and every complete Pattern payload. -/
theorem patternOptionTerm_injective : Function.Injective patternOptionTerm := by
  intro left right same
  cases left <;> cases right <;>
    simp_all [patternOptionTerm, InferenceCettaWire.encodePattern_injective.eq_iff]

def bindingsOptionTerm : Option Bindings → Term
  | none => .symbol "None"
  | some bindings => .application "Some" [bindingsTerm bindings]

private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev patternValue (pattern : Pattern) : Atom :=
  encoded (InferenceCettaWire.encodePattern pattern)
private abbrev bindingsValue (bindings : Bindings) : Atom := encoded (bindingsTerm bindings)

/-- The labels of the retained two-argument helpers. They select source
equations, not an additional evaluator. -/
private inductive Helper where
  | binding | merge | bind | children

private def Helper.head : Helper → String
  | .binding => "gslt:automata:binding"
  | .merge => "gslt:automata:merge"
  | .bind => "gslt:automata:bind"
  | .children => "gslt:automata:bind-children"

private def Helper.first : Helper → String
  | .binding => "name"
  | .merge => "left"
  | .bind => "pattern"
  | .children => "patterns"

private def Helper.second : Helper → String
  | .binding => "bindings"
  | .merge => "right"
  | .bind => "subject"
  | .children => "subjects"

attribute [local simp] a v encoded patternValue bindingsValue
  Helper.head Helper.first Helper.second Effects.boolean List.find?_cons

private def helperEquation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def environment (helper : Helper) (left right : Term) : Subst :=
  [(helper.second, encoded right), (helper.first, encoded left)]

private theorem helper_clause (helper : Helper) (left right : Term) :
    clauses program helper.head [encoded left, encoded right] =
      [.evaluate (environment helper left right) (helperEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  have unique : equations helper.head = [helperEquation helper] := by cases helper <;> rfl
  have formals : (helperEquation helper).arguments = [v helper.first, v helper.second] := by
    cases helper <;> decide +kernel
  rw [unique]
  cases helper <;> simp [formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
    environment, Helper.first, Helper.second]

private theorem helper_call (helper : Helper) (bindings : Subst) (state : State)
    (left right : Term) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst bindings) = [encoded left, encoded right])
    (length : arguments.length = 2)
    (computed : PureReturns program (environment helper left right) state
      (helperEquation helper).body state answer) :
    PureReturns program bindings state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program bindings (environment helper left right) state state
    helper.head arguments (helperEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide) (by cases helper <;> decide +kernel) _ _ computed
  · intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> cases helper <;> decide +kernel
  · rw [captured]
    exact helper_clause helper left right

private theorem some_variable_template (name : String) :
    PureData.Template program (a "Some" [v name]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .captured _

private def bindingCons : Atom :=
  a "if" [a "==" [v "name", v "key"], a "Some" [v "value"],
    a "gslt:automata:binding" [v "name", v "rest"]]

private def bindingCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "None"),
    (a "LCons" [a "Binding" [v "key", v "value"], v "rest"], bindingCons)]

private theorem binding_shape : (helperEquation .binding).body =
    a "case" [v "bindings", .expression (bindingCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem lookup_cons (name key : String) (value : Pattern) (rest : Bindings) :
    Bindings.lookup ((key, value) :: rest) name =
      if key = name then some value else Bindings.lookup rest name := by
  simp only [Bindings.lookup, List.find?_cons]
  split <;> simp_all

/-- Opaque payloads use the same binding rows as canonical Pattern values. -/
def payloadBindingTerm (binding : String × Term) : Term :=
  .application "Binding" [.string binding.1, binding.2]

def payloadBindingsTerm (bindings : List (String × Term)) : Term :=
  encodeList payloadBindingTerm bindings

def payloadOptionTerm : Option Term → Term
  | none => .symbol "None"
  | some value => .application "Some" [value]

/-- First-name lookup does not interpret or normalize a stored payload. -/
def payloadLookup (bindings : List (String × Term)) (name : String) : Option Term :=
  (bindings.find? (fun entry => entry.1 == name)).map (·.2)

private theorem payloadLookup_cons (name key : String) (value : Term)
    (rest : List (String × Term)) :
    payloadLookup ((key, value) :: rest) name =
      if key = name then some value else payloadLookup rest name := by
  simp only [payloadLookup, List.find?_cons]
  split <;> simp_all

private theorem payloadBindingsTerm_pattern_map (bindings : Bindings) :
    payloadBindingsTerm (bindings.map fun entry => (entry.1, InferenceCettaWire.encodePattern entry.2)) =
      bindingsTerm bindings := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      simpa [payloadBindingsTerm, bindingsTerm, encodeList, payloadBindingTerm, bindingTerm] using
        congrArg (fun tail => Term.application "LCons" [bindingTerm entry, tail]) ih

private theorem payloadLookup_pattern_map (bindings : Bindings) (name : String) :
    payloadLookup (bindings.map fun entry => (entry.1, InferenceCettaWire.encodePattern entry.2)) name =
      (bindings.lookup name).map InferenceCettaWire.encodePattern := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [List.map_cons, payloadLookup_cons, lookup_cons]
      split <;> simp_all

private theorem payloadOptionTerm_pattern_map (value : Option Pattern) :
    payloadOptionTerm (value.map InferenceCettaWire.encodePattern) = patternOptionTerm value := by
  cases value <;> rfl

private theorem payload_binding_body_returns (state : State) (name : String) (bindings : List (String × Term)) :
    PureReturns program (environment .binding (.string name) (payloadBindingsTerm bindings)) state
      (helperEquation .binding).body state (encoded (payloadOptionTerm (payloadLookup bindings name))) := by
  induction bindings with
  | nil =>
      rw [binding_shape]
      apply case_returns program (environment .binding (.string name) (payloadBindingsTerm []))
        (environment .binding (.string name) (payloadBindingsTerm [])) state state state
        (v "bindings") (.symbol "LNil") (.symbol "None") (.symbol "None") _ bindingCases
        (read_cases_encoded _) _ _ _
      · simpa [environment, Helper.second, Helper.first, applySubst, Subst.lookup, payloadBindingsTerm]
          using variable_returns program (environment .binding (.string name) (payloadBindingsTerm [])) state "bindings"
      · simp [bindingCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program _ state "None"
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      let bindings := environment .binding (.string name) (payloadBindingsTerm ((key, value) :: rest))
      let selected := ("rest", encoded (payloadBindingsTerm rest)) :: ("value", encoded value) ::
        ("key", encoded (.string key)) :: bindings
      rw [binding_shape]
      apply case_returns program bindings selected state state state (v "bindings")
        (encoded (payloadBindingsTerm ((key, value) :: rest))) bindingCons
        (encoded (payloadOptionTerm (payloadLookup ((key, value) :: rest) name))) _ bindingCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, Helper.second, Helper.first, applySubst, Subst.lookup]
          using variable_returns program bindings state "bindings"
      · simp [bindingCases, payloadBindingsTerm, payloadBindingTerm, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
          bindings, environment, Helper.second, Helper.first]
      · have tested := CettaWireAtom.equality_captured_returns program selected state
          (.string name) (.string key) "name" "key"
          (by simp [selected, bindings, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
          (by simp [selected, applySubst, Subst.lookup])
        apply if_returns program selected state state state _ _ _ _ _ tested
        by_cases same : key = name
        · simpa [bindingCons, same, payloadLookup_cons, payloadOptionTerm, applySubst,
            applySubst.applySubstList, Subst.lookup, selected, bindings, environment,
            Helper.first, Helper.second, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            using PureData.template_return program selected state _ (some_variable_template "value")
        · have recursive := helper_call .binding selected state (.string name) (payloadBindingsTerm rest)
            [v "name", v "rest"] (encoded (payloadOptionTerm (payloadLookup rest name)))
            (by simp [selected, bindings, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
            rfl ih
          simpa [bindingCons, same, Ne.symm same, payloadLookup_cons] using recursive

private theorem binding_body_returns (state : State) (name : String) (bindings : Bindings) :
    PureReturns program (environment .binding (.string name) (bindingsTerm bindings)) state
      (helperEquation .binding).body state (encoded (patternOptionTerm (bindings.lookup name))) := by
  simpa only [payloadBindingsTerm_pattern_map, payloadLookup_pattern_map,
    payloadOptionTerm_pattern_map] using
    payload_binding_body_returns state name
      (bindings.map fun entry => (entry.1, InferenceCettaWire.encodePattern entry.2))

/-- Execute the retained lookup on arbitrary literal constructor data. -/
theorem payload_binding_returns (state : State) (name : String)
    (bindings : List (String × Term)) :
    PureReturns program [] state
      (a "gslt:automata:binding" [encoded (.string name), encoded (payloadBindingsTerm bindings)]) state
      (encoded (payloadOptionTerm (payloadLookup bindings name))) :=
  helper_call .binding [] state (.string name) (payloadBindingsTerm bindings) _ _ (by simp) rfl
    (payload_binding_body_returns state name bindings)

theorem payload_binding_captured_returns (caller : Subst) (state : State) (name : String)
    (bindings : List (String × Term)) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (.string name), encoded (payloadBindingsTerm bindings)]) :
    PureReturns program caller state (a "gslt:automata:binding" arguments) state
      (encoded (payloadOptionTerm (payloadLookup bindings name))) := by
  have length : arguments.length = 2 := by
    have := congrArg List.length captured
    simpa using this
  exact helper_call .binding caller state (.string name) (payloadBindingsTerm bindings)
    arguments _ captured length (payload_binding_body_returns state name bindings)

/-- Source lookup preserves the first matching entry of the canonical binding list. -/
theorem binding_returns (state : State) (name : String) (bindings : Bindings) :
    PureReturns program [] state
      (a "gslt:automata:binding" [encoded (.string name), bindingsValue bindings]) state
      (encoded (patternOptionTerm (bindings.lookup name))) :=
  helper_call .binding [] state (.string name) (bindingsTerm bindings) _ _ (by simp) rfl
    (binding_body_returns state name bindings)

private def mergeMissing : Atom :=
  a "let" [v "next", a "LCons" [a "Binding" [v "name", v "value"], v "left"],
    a "gslt:automata:merge" [v "next", v "rest"]]
private def mergeFound : Atom :=
  a "if" [a "==" [v "found", v "value"],
    a "gslt:automata:merge" [v "left", v "rest"], .symbol "None"]
private def mergeLookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", mergeMissing), (a "Some" [v "found"], mergeFound)]
private def mergeCons : Atom :=
  a "case" [a "gslt:automata:binding" [v "name", v "left"],
    .expression (mergeLookupCases.map fun row => .expression [row.1, row.2])]
private def mergeCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "Some" [v "left"]),
    (a "LCons" [a "Binding" [v "name", v "value"], v "rest"], mergeCons)]

private theorem merge_shape : (helperEquation .merge).body =
    a "case" [v "right", .expression (mergeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem merge_cons (left : Bindings) (name : String) (value : Pattern) (rest : Bindings) :
    mergeBindings left ((name, value) :: rest) =
      match Bindings.lookup left name with
      | none => mergeBindings ((name, value) :: left) rest
      | some existing => if existing = value then mergeBindings left rest else none := by
  simp only [mergeBindings, List.foldlM_cons, Bindings.lookup]
  cases found : left.find? (fun entry => entry.1 == name) with
  | none => simp
  | some entry =>
      obtain ⟨key, existing⟩ := entry
      simp
      split <;> simp_all

private theorem next_template : PureData.Template program
    (a "LCons" [a "Binding" [v "name", v "value"], v "left"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Binding" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .captured _
  · exact .captured _

private theorem merge_body_returns (state : State) (left right : Bindings) :
    PureReturns program (environment .merge (bindingsTerm left) (bindingsTerm right)) state
      (helperEquation .merge).body state (encoded (bindingsOptionTerm (mergeBindings left right))) := by
  induction right generalizing left with
  | nil =>
      rw [merge_shape]
      apply case_returns program (environment .merge (bindingsTerm left) (bindingsTerm []))
        (environment .merge (bindingsTerm left) (bindingsTerm [])) state state state
        (v "right") (.symbol "LNil") (a "Some" [v "left"])
        (encoded (bindingsOptionTerm (some left))) _ mergeCases (read_cases_encoded _) _ _ _
      · simpa [environment, Helper.second, Helper.first, applySubst, Subst.lookup, bindingsTerm]
          using variable_returns program (environment .merge (bindingsTerm left) (bindingsTerm [])) state "right"
      · simp [mergeCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [environment, Helper.second, Helper.first, applySubst, applySubst.applySubstList,
          Subst.lookup, bindingsOptionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          using PureData.template_return program
            (environment .merge (bindingsTerm left) (bindingsTerm [])) state _
            (some_variable_template "left")
  | cons entry rest ih =>
      obtain ⟨name, value⟩ := entry
      let bindings := environment .merge (bindingsTerm left) (bindingsTerm ((name, value) :: rest))
      let selected := ("rest", bindingsValue rest) :: ("value", patternValue value) ::
        ("name", encoded (.string name)) :: bindings
      have looked := helper_call .binding selected state (.string name) (bindingsTerm left)
        [v "name", v "left"] (encoded (patternOptionTerm (left.lookup name)))
        (by simp [selected, bindings, environment, Helper.first, Helper.second, applySubst, Subst.lookup])
        rfl (binding_body_returns state name left)
      rw [merge_shape]
      apply case_returns program bindings selected state state state (v "right")
        (bindingsValue ((name, value) :: rest)) mergeCons
        (encoded (bindingsOptionTerm (mergeBindings left ((name, value) :: rest)))) _ mergeCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, environment, Helper.second, Helper.first, applySubst, Subst.lookup]
          using variable_returns program bindings state "right"
      · simp [mergeCases, bindingsTerm, bindingTerm, encodeList, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
          bindings, environment, Helper.second, Helper.first]
      · cases found : left.lookup name with
        | none =>
            apply case_returns program selected selected state state state
              (a "gslt:automata:binding" [v "name", v "left"]) (.symbol "None") mergeMissing
              (encoded (bindingsOptionTerm (mergeBindings left ((name, value) :: rest))))
              _ mergeLookupCases (read_cases_encoded _)
              (by simpa [found, patternOptionTerm, CettaWireAtom.encode] using looked) _ _
            · simp [mergeLookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · let bound := ("next", bindingsValue ((name, value) :: left)) :: selected
              apply let_returns program selected bound state state state (v "next")
                (a "LCons" [a "Binding" [v "name", v "value"], v "left"])
                (a "gslt:automata:merge" [v "next", v "rest"])
                (bindingsValue ((name, value) :: left)) _
              · simpa [applySubst, applySubst.applySubstList, Subst.lookup, selected, bindings,
                  environment, Helper.first, Helper.second, bindingsTerm, bindingTerm,
                  encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                  using PureData.template_return program selected state _ next_template
              · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected,
                  bindings, environment]
              · have recursive := helper_call .merge bound state (bindingsTerm ((name, value) :: left))
                  (bindingsTerm rest) [v "next", v "rest"]
                  (encoded (bindingsOptionTerm (mergeBindings ((name, value) :: left) rest)))
                  (by simp [bound, selected, applySubst, Subst.lookup]) rfl (ih ((name, value) :: left))
                simpa [merge_cons, found] using recursive
        | some existing =>
            let checked := ("found", patternValue existing) :: selected
            apply case_returns program selected checked state state state
              (a "gslt:automata:binding" [v "name", v "left"])
              (encoded (patternOptionTerm (some existing))) mergeFound
              (encoded (bindingsOptionTerm (mergeBindings left ((name, value) :: rest))))
              _ mergeLookupCases (read_cases_encoded _) (by simpa [found] using looked) _ _
            · simp [mergeLookupCases, patternOptionTerm, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, checked,
                selected, bindings, environment]
            · have tested := CettaWireAtom.equality_captured_returns program checked state
                (InferenceCettaWire.encodePattern existing) (InferenceCettaWire.encodePattern value)
                "found" "value" (by simp [checked, applySubst, Subst.lookup])
                (by simp [checked, selected, applySubst, Subst.lookup])
              have exactness : InferenceCettaWire.encodePattern existing =
                  InferenceCettaWire.encodePattern value ↔ existing = value :=
                InferenceCettaWire.encodePattern_injective.eq_iff
              simp only [exactness] at tested
              apply if_returns program checked state state state _ _ _ _ _ tested
              by_cases same : existing = value
              · have recursive := helper_call .merge checked state (bindingsTerm left) (bindingsTerm rest)
                  [v "left", v "rest"] (encoded (bindingsOptionTerm (mergeBindings left rest)))
                  (by simp [checked, selected, bindings, environment, Helper.first, Helper.second,
                    applySubst, Subst.lookup]) rfl (ih left)
                simpa [same, merge_cons, found] using recursive
              · simpa [same, merge_cons, found, bindingsOptionTerm, CettaWireAtom.encode]
                  using symbol_returns program checked state "None"

/-- The retained merge agrees with canonical consistency checking for every
ordered binding list, not just bindings produced by the structural automata. -/
theorem merge_returns (state : State) (left right : Bindings) :
    PureReturns program [] state
      (a "gslt:automata:merge" [bindingsValue left, bindingsValue right]) state
      (encoded (bindingsOptionTerm (mergeBindings left right))) :=
  helper_call .merge [] state (bindingsTerm left) (bindingsTerm right) _ _ (by simp) rfl
    (merge_body_returns state left right)

private theorem some_nil_template : PureData.Template program (a "Some" [.symbol "LNil"]) := by
  apply PureData.Template.constructor "Some" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_singleton] at member
  subst argument
  exact .symbol _

private def bindVariable : Atom :=
  a "Some" [a "LCons" [a "Binding" [v "name", v "subject"], .symbol "LNil"]]
private def bindBound : Atom :=
  a "if" [a "==" [v "pattern", v "subject"], a "Some" [.symbol "LNil"], .symbol "None"]
private def bindApplication : Atom :=
  a "if" [a "==" [v "head", v "actual"],
    a "gslt:automata:bind-children" [v "children", v "arguments"], .symbol "None"]
private def bindSubjectCases : SpaceSemantics.Cases :=
  [(a "PApp" [v "actual", v "arguments"], bindApplication), (v "other", .symbol "None")]
private def bindApplicationCase : Atom :=
  a "case" [v "subject", .expression (bindSubjectCases.map fun row => .expression [row.1, row.2])]
private def bindCases : SpaceSemantics.Cases :=
  [(a "FVar" [v "name"], bindVariable),
    (a "Var" [v "index"], bindBound),
    (a "PApp" [v "head", v "children"], bindApplicationCase)]

private theorem bind_shape : (helperEquation .bind).body =
    a "case" [v "pattern", .expression (bindCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem variable_template : PureData.Template program bindVariable := by
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

private def childrenResultCases : SpaceSemantics.Cases :=
  [(.expression [a "Some" [v "head"], a "Some" [v "tail"]],
    a "gslt:automata:merge" [v "head", v "tail"]),
    (v "bad", .symbol "None")]
private def childrenCons : Atom :=
  a "case" [.expression [a "gslt:automata:bind" [v "p", v "s"],
      a "gslt:automata:bind-children" [v "ps", v "ss"]],
    .expression (childrenResultCases.map fun row => .expression [row.1, row.2])]
private def childrenCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "LNil", .symbol "LNil"], a "Some" [.symbol "LNil"]),
    (.expression [a "LCons" [v "p", v "ps"], a "LCons" [v "s", v "ss"]], childrenCons),
    (v "bad", .symbol "None")]

private theorem children_shape : (helperEquation .children).body =
    a "case" [.expression [v "patterns", v "subjects"],
      .expression (childrenCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem patternList_value (patterns : List PatternPlan) :
    encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns)) =
      encoded (encodeList (fun pattern : PatternPlan => InferenceCettaWire.encodePattern pattern.erase) patterns) := by
  congr 1
  rw [InferenceCettaWire.encodePatterns_eq_encodeList, erasePatterns_eq_map, encodeList_map]
  rfl

private theorem args_nil_of_length_ne (patterns subjects : List Pattern)
    (different : patterns.length ≠ subjects.length) : matchArgs patterns subjects = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro bindings member
  exact different (Mettapedia.OSLF.MeTTaIL.MatchSpec.matchArgs_sound member).length_eq

private theorem application_match (head actual : String) (patterns subjects : List PatternPlan) :
    matchPattern (.apply head (erasePatterns patterns)) (.apply actual (erasePatterns subjects)) =
      if head = actual then matchArgs (erasePatterns patterns) (erasePatterns subjects) else [] := by
  simp only [matchPattern]
  by_cases sameHead : head = actual
  · subst actual
    by_cases sameLength : (erasePatterns patterns).length = (erasePatterns subjects).length
    · simp [sameLength]
    · simp [args_nil_of_length_ne _ _ sameLength]
  · simp [sameHead]

private theorem bound_match (index : Nat) (subject : PatternPlan) :
    matchPattern (.bvar index) subject.erase =
      if (.bvar index : Pattern) = subject.erase then [[]] else [] := by
  cases subject <;> simp [PatternPlan.erase, matchPattern]

private theorem result_pair_returns (bindings : Subst) (state : State)
    (headResult tailResult : Option Bindings)
    (headComputed : PureReturns program bindings state
      (a "gslt:automata:bind" [v "p", v "s"]) state (encoded (bindingsOptionTerm headResult)))
    (tailComputed : PureReturns program bindings state
      (a "gslt:automata:bind-children" [v "ps", v "ss"]) state (encoded (bindingsOptionTerm tailResult))) :
    PureReturns program bindings state
      (.expression [a "gslt:automata:bind" [v "p", v "s"],
        a "gslt:automata:bind-children" [v "ps", v "ss"]]) state
      (.expression [encoded (bindingsOptionTerm headResult), encoded (bindingsOptionTerm tailResult)]) := by
  refine .step (step_transition rfl) ?_
  exact PureData.arguments_return program bindings state _ _
    (.cons headComputed (.cons tailComputed .nil)) [] 0

private abbrev patternsTerm (patterns : List PatternPlan) : Term :=
  InferenceCettaWire.encodePatterns (erasePatterns patterns)

private abbrev patternsValue (patterns : List PatternPlan) : Atom := encoded (patternsTerm patterns)

mutual
  private theorem bind_body_exact (state : State) (pattern subject : PatternPlan) :
      ∃ result : Option Bindings,
        matchPattern pattern.erase subject.erase = result.toList ∧
        PureReturns program
          (environment .bind (InferenceCettaWire.encodePattern pattern.erase)
            (InferenceCettaWire.encodePattern subject.erase)) state
          (helperEquation .bind).body state (encoded (bindingsOptionTerm result)) := by
    cases pattern with
    | metavariable name =>
        refine ⟨some [(name, subject.erase)], by simp [PatternPlan.erase, matchPattern], ?_⟩
        let bindings := environment .bind (InferenceCettaWire.encodePattern (.fvar name))
          (InferenceCettaWire.encodePattern subject.erase)
        let selected := ("name", encoded (.string name)) :: bindings
        rw [bind_shape]
        apply case_returns program bindings selected state state state (v "pattern")
          (patternValue (.fvar name)) bindVariable
          (encoded (bindingsOptionTerm (some [(name, subject.erase)]))) _ bindCases
          (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup]
            using variable_returns program bindings state "pattern"
        · simp [bindCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
            bindings, environment]
        · simpa [bindVariable, bindingsOptionTerm, bindingsTerm, bindingTerm, encodeList,
            applySubst, applySubst.applySubstList, Subst.lookup, selected, bindings,
            environment, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            using PureData.template_return program selected state _ variable_template
    | bound index =>
        let result : Option Bindings := if (.bvar index : Pattern) = subject.erase then some [] else none
        refine ⟨result, by simp [PatternPlan.erase, bound_match, result]; split <;> rfl, ?_⟩
        let bindings := environment .bind (InferenceCettaWire.encodePattern (.bvar index))
          (InferenceCettaWire.encodePattern subject.erase)
        let selected := ("index", encoded (.natural index)) :: bindings
        rw [bind_shape]
        apply case_returns program bindings selected state state state (v "pattern")
          (patternValue (.bvar index)) bindBound (encoded (bindingsOptionTerm result))
          _ bindCases (read_cases_encoded _) _ _ _
        · simpa [bindings, environment, applySubst, Subst.lookup]
            using variable_returns program bindings state "pattern"
        · simp [bindCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
            bindings, environment]
        · have tested := CettaWireAtom.equality_captured_returns program selected state
            (InferenceCettaWire.encodePattern (.bvar index))
            (InferenceCettaWire.encodePattern subject.erase) "pattern" "subject"
            (by simp [selected, bindings, environment, applySubst, Subst.lookup])
            (by simp [selected, bindings, environment, applySubst, Subst.lookup])
          have exactness : InferenceCettaWire.encodePattern (.bvar index) =
              InferenceCettaWire.encodePattern subject.erase ↔ (.bvar index : Pattern) = subject.erase :=
            InferenceCettaWire.encodePattern_injective.eq_iff
          simp only [exactness] at tested
          apply if_returns program selected state state state _ _ _ _ _ tested
          by_cases same : (.bvar index : Pattern) = subject.erase
          · simpa [same, result, bindBound, bindingsOptionTerm, bindingsTerm, encodeList,
              applySubst, applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
              using PureData.template_return program selected state _ some_nil_template
          · simpa [same, result, bindBound, bindingsOptionTerm, CettaWireAtom.encode]
              using symbol_returns program selected state "None"
    | application head patterns =>
        let bindings := environment .bind (InferenceCettaWire.encodePattern (.apply head (erasePatterns patterns)))
          (InferenceCettaWire.encodePattern subject.erase)
        let selected := ("children", patternsValue patterns) :: ("head", encoded (.string head)) :: bindings
        have patternComputed : PureReturns program bindings state (v "pattern") state
            (patternValue (.apply head (erasePatterns patterns))) := by
          simpa [bindings, environment, applySubst, Subst.lookup]
            using variable_returns program bindings state "pattern"
        have patternSelected : SpaceSemantics.selectCase bindings
            (patternValue (.apply head (erasePatterns patterns))) bindCases =
            some (selected, bindApplicationCase) := by
          simp [bindCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
            bindings, environment]
        cases subject with
        | application actual subjects =>
            obtain ⟨childResult, matchedChildren, childComputed⟩ := children_body_exact state patterns subjects
            let result : Option Bindings := if head = actual then childResult else none
            refine ⟨result, ?_, ?_⟩
            · simp only [PatternPlan.erase, application_match]
              by_cases same : head = actual <;> simp [same, result, matchedChildren]
            · rw [bind_shape]
              apply case_returns program bindings selected state state state (v "pattern")
                (patternValue (.apply head (erasePatterns patterns))) bindApplicationCase
                (encoded (bindingsOptionTerm result)) _ bindCases (read_cases_encoded _)
                patternComputed patternSelected
              let checked := ("arguments", patternsValue subjects) ::
                ("actual", encoded (.string actual)) :: selected
              apply case_returns program selected checked state state state (v "subject")
                (patternValue (.apply actual (erasePatterns subjects))) bindApplication
                (encoded (bindingsOptionTerm result)) _ bindSubjectCases (read_cases_encoded _) _ _ _
              · simpa [selected, bindings, environment, PatternPlan.erase, applySubst, Subst.lookup]
                  using variable_returns program selected state "subject"
              · simp [bindSubjectCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
                  CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                  SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, checked,
                  selected, bindings, environment]
              · have tested := CettaWireAtom.equality_captured_returns program checked state
                  (.string head) (.string actual) "head" "actual"
                  (by simp [checked, selected, applySubst, Subst.lookup])
                  (by simp [checked, applySubst, Subst.lookup])
                simp only [Term.string.injEq] at tested
                apply if_returns program checked state state state _ _ _ _ _ tested
                by_cases same : head = actual
                · have recursive := helper_call .children checked state (patternsTerm patterns)
                    (patternsTerm subjects) [v "children", v "arguments"]
                    (encoded (bindingsOptionTerm childResult))
                    (by simp [checked, selected, applySubst, Subst.lookup]) rfl childComputed
                  simpa [result, same] using recursive
                · simpa [result, same, bindingsOptionTerm, CettaWireAtom.encode]
                    using symbol_returns program checked state "None"
        | metavariable name =>
            refine ⟨none, by simp [PatternPlan.erase, matchPattern], ?_⟩
            rw [bind_shape]
            apply case_returns program bindings selected state state state (v "pattern")
              (patternValue (.apply head (erasePatterns patterns))) bindApplicationCase
              (encoded (bindingsOptionTerm none)) _ bindCases (read_cases_encoded _)
              patternComputed patternSelected
            let checked := ("other", patternValue (.fvar name)) :: selected
            apply case_returns program selected checked state state state (v "subject")
              (patternValue (.fvar name)) (.symbol "None") (encoded (bindingsOptionTerm none))
              _ bindSubjectCases (read_cases_encoded _) _ _ _
            · simpa [selected, bindings, environment, PatternPlan.erase, applySubst, Subst.lookup]
                using variable_returns program selected state "subject"
            · simp [bindSubjectCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, checked,
                selected, bindings, environment]
            · exact symbol_returns program checked state "None"
        | bound index =>
            refine ⟨none, by simp [PatternPlan.erase, matchPattern], ?_⟩
            rw [bind_shape]
            apply case_returns program bindings selected state state state (v "pattern")
              (patternValue (.apply head (erasePatterns patterns))) bindApplicationCase
              (encoded (bindingsOptionTerm none)) _ bindCases (read_cases_encoded _)
              patternComputed patternSelected
            let checked := ("other", patternValue (.bvar index)) :: selected
            apply case_returns program selected checked state state state (v "subject")
              (patternValue (.bvar index)) (.symbol "None") (encoded (bindingsOptionTerm none))
              _ bindSubjectCases (read_cases_encoded _) _ _ _
            · simpa [selected, bindings, environment, PatternPlan.erase, applySubst, Subst.lookup]
                using variable_returns program selected state "subject"
            · simp [bindSubjectCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
                CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, checked,
                selected, bindings, environment]
            · exact symbol_returns program checked state "None"
  termination_by 2 * pattern.work
  decreasing_by simp [PatternPlan.work]; omega

  private theorem children_body_exact (state : State) (patterns subjects : List PatternPlan) :
      ∃ result : Option Bindings,
        matchArgs (erasePatterns patterns) (erasePatterns subjects) = result.toList ∧
        PureReturns program (environment .children (patternsTerm patterns) (patternsTerm subjects)) state
          (helperEquation .children).body state (encoded (bindingsOptionTerm result)) := by
    let bindings := environment .children (patternsTerm patterns) (patternsTerm subjects)
    have tupleComputed : PureReturns program bindings state (.expression [v "patterns", v "subjects"]) state
        (.expression [patternsValue patterns, patternsValue subjects]) := by
      simpa [bindings, environment, applySubst, Subst.lookup]
        using tuple_variables_return program bindings state ["patterns", "subjects"]
    cases patterns with
    | nil =>
        cases subjects with
        | nil =>
            refine ⟨some [], by simp [erasePatterns, matchArgs], ?_⟩
            rw [children_shape]
            apply case_returns program bindings bindings state state state _
              (.expression [patternsValue [], patternsValue []]) (a "Some" [.symbol "LNil"])
              (encoded (bindingsOptionTerm (some []))) _ childrenCases (read_cases_encoded _)
              tupleComputed _ _
            · simp [childrenCases, patternsValue, patternsTerm, erasePatterns,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom]
            · simpa [bindingsOptionTerm, bindingsTerm, encodeList,
                applySubst, applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                using PureData.template_return program bindings state _ some_nil_template
        | cons s ss =>
            refine ⟨none, by simp [erasePatterns, matchArgs], ?_⟩
            rw [children_shape]
            let selected := ("bad", .expression [patternsValue [], patternsValue (s :: ss)]) :: bindings
            apply case_returns program bindings selected state state state _
              (.expression [patternsValue [], patternsValue (s :: ss)]) (.symbol "None")
              (encoded (bindingsOptionTerm none)) _ childrenCases (read_cases_encoded _) tupleComputed _ _
            · simp [childrenCases, patternsValue, patternsTerm, erasePatterns,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, selected, bindings, environment]
            · exact symbol_returns program selected state "None"
    | cons p ps =>
        cases subjects with
        | nil =>
            refine ⟨none, by simp [erasePatterns, matchArgs], ?_⟩
            rw [children_shape]
            let selected := ("bad", .expression [patternsValue (p :: ps), patternsValue []]) :: bindings
            apply case_returns program bindings selected state state state _
              (.expression [patternsValue (p :: ps), patternsValue []]) (.symbol "None")
              (encoded (bindingsOptionTerm none)) _ childrenCases (read_cases_encoded _) tupleComputed _ _
            · simp [childrenCases, patternsValue, patternsTerm, erasePatterns,
                InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, selected, bindings, environment]
            · exact symbol_returns program selected state "None"
        | cons s ss =>
            obtain ⟨headResult, headMatches, headComputed⟩ := bind_body_exact state p s
            obtain ⟨tailResult, tailMatches, tailComputed⟩ := children_body_exact state ps ss
            let result := headResult.bind fun head => tailResult.bind (mergeBindings head)
            refine ⟨result, ?_, ?_⟩
            · simp only [erasePatterns, matchArgs, headMatches, tailMatches]
              cases headResult <;> cases tailResult <;> simp [result, List.filterMap]
              rfl
            · let selected := ("ss", patternsValue ss) :: ("s", patternValue s.erase) ::
                ("ps", patternsValue ps) :: ("p", patternValue p.erase) :: bindings
              have headCall := helper_call .bind selected state (InferenceCettaWire.encodePattern p.erase)
                (InferenceCettaWire.encodePattern s.erase) [v "p", v "s"]
                (encoded (bindingsOptionTerm headResult))
                (by simp [selected, applySubst, Subst.lookup]) rfl headComputed
              have tailCall := helper_call .children selected state (patternsTerm ps) (patternsTerm ss)
                [v "ps", v "ss"] (encoded (bindingsOptionTerm tailResult))
                (by simp [selected, applySubst, Subst.lookup]) rfl tailComputed
              have pairComputed := result_pair_returns selected state headResult tailResult headCall tailCall
              rw [children_shape]
              apply case_returns program bindings selected state state state _
                (.expression [patternsValue (p :: ps), patternsValue (s :: ss)]) childrenCons
                (encoded (bindingsOptionTerm result)) _ childrenCases (read_cases_encoded _) tupleComputed _ _
              · simp [childrenCases, patternsValue, patternsTerm, erasePatterns,
                  InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, selected, bindings, environment]
              · cases headResult with
                | none =>
                    let checked := ("bad", .expression [encoded (bindingsOptionTerm none),
                      encoded (bindingsOptionTerm tailResult)]) :: selected
                    apply case_returns program selected checked state state state _
                      (.expression [encoded (bindingsOptionTerm none), encoded (bindingsOptionTerm tailResult)])
                      (.symbol "None") (encoded (bindingsOptionTerm result)) _ childrenResultCases
                      (read_cases_encoded _) pairComputed _ _
                    · simp [childrenResultCases, bindingsOptionTerm, CettaWireAtom.encode,
                        SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                        checked, selected, bindings, environment]
                    · simpa [result, bindingsOptionTerm, CettaWireAtom.encode]
                        using symbol_returns program checked state "None"
                | some head =>
                    cases tailResult with
                    | none =>
                        let checked := ("bad", .expression [encoded (bindingsOptionTerm (some head)),
                          encoded (bindingsOptionTerm none)]) :: selected
                        apply case_returns program selected checked state state state _
                          (.expression [encoded (bindingsOptionTerm (some head)), encoded (bindingsOptionTerm none)])
                          (.symbol "None") (encoded (bindingsOptionTerm result)) _ childrenResultCases
                          (read_cases_encoded _) pairComputed _ _
                        · simp [childrenResultCases, bindingsOptionTerm, CettaWireAtom.encode,
                            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                            checked, selected, bindings, environment]
                        · simpa [result, bindingsOptionTerm, CettaWireAtom.encode]
                            using symbol_returns program checked state "None"
                    | some tail =>
                        let checked := ("tail", bindingsValue tail) :: ("head", bindingsValue head) :: selected
                        apply case_returns program selected checked state state state _
                          (.expression [encoded (bindingsOptionTerm (some head)), encoded (bindingsOptionTerm (some tail))])
                          (a "gslt:automata:merge" [v "head", v "tail"])
                          (encoded (bindingsOptionTerm result)) _ childrenResultCases
                          (read_cases_encoded _) pairComputed _ _
                        · simp [childrenResultCases, bindingsOptionTerm, CettaWireAtom.encode,
                            CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                            SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                            checked, selected, bindings, environment]
                        · have merged := helper_call .merge checked state (bindingsTerm head) (bindingsTerm tail)
                            [v "head", v "tail"] (encoded (bindingsOptionTerm (mergeBindings head tail)))
                            (by simp [checked, applySubst, Subst.lookup]) rfl (merge_body_returns state head tail)
                          simpa [result] using merged
  termination_by 2 * patternPlansWork patterns + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos p
      rw [patternPlansWork]
      omega
end

/-- The retained single-pattern helper returns exactly the singleton-or-empty
canonical first-order match, with its binding-list order unchanged. -/
theorem bind_returns (state : State) (pattern subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:bind" [patternValue pattern.erase, patternValue subject.erase]) state
      (encoded (bindingsOptionTerm (matchPattern pattern.erase subject.erase).head?)) := by
  obtain ⟨result, matched, computed⟩ := bind_body_exact state pattern subject
  have chosen : (matchPattern pattern.erase subject.erase).head? = result := by
    rw [matched]
    cases result <;> rfl
  rw [chosen]
  exact helper_call .bind [] state (InferenceCettaWire.encodePattern pattern.erase)
    (InferenceCettaWire.encodePattern subject.erase) _ _ (by simp) rfl computed

theorem bind_matches_singleton (pattern subject : PatternPlan) :
    (matchPattern pattern.erase subject.erase).head?.toList = matchPattern pattern.erase subject.erase := by
  obtain ⟨result, matched, _⟩ := bind_body_exact Effects.empty pattern subject
  rw [matched]
  cases result <;> rfl

/-- The ordered child-vector helper has the same exact canonical contract. -/
theorem bind_children_returns (state : State) (patterns subjects : List PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:bind-children" [patternsValue patterns, patternsValue subjects]) state
      (encoded (bindingsOptionTerm (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head?)) := by
  obtain ⟨result, matched, computed⟩ := children_body_exact state patterns subjects
  have chosen : (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head? = result := by
    rw [matched]
    cases result <;> rfl
  rw [chosen]
  exact helper_call .children [] state (patternsTerm patterns) (patternsTerm subjects) _ _ (by simp) rfl computed

theorem bind_children_matches_singleton (patterns subjects : List PatternPlan) :
    (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head?.toList =
      matchArgs (erasePatterns patterns) (erasePatterns subjects) := by
  obtain ⟨result, matched, _⟩ := children_body_exact Effects.empty patterns subjects
  rw [matched]
  cases result <;> rfl

theorem binding_captured_returns (caller : Subst) (state : State) (name : String)
    (bindings : Bindings) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded (.string name), bindingsValue bindings]) :
    PureReturns program caller state (a "gslt:automata:binding" arguments) state
      (encoded (patternOptionTerm (Bindings.lookup bindings name))) := by
  have length : arguments.length = 2 := by
    have := congrArg List.length captured
    simpa using this
  exact helper_call .binding caller state (.string name) (bindingsTerm bindings) arguments _ captured length
    (binding_body_returns state name bindings)

theorem merge_captured_returns (caller : Subst) (state : State) (left right : Bindings)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [bindingsValue left, bindingsValue right]) :
    PureReturns program caller state (a "gslt:automata:merge" arguments) state
      (encoded (bindingsOptionTerm (mergeBindings left right))) := by
  have length : arguments.length = 2 := by
    have := congrArg List.length captured
    simpa using this
  exact helper_call .merge caller state (bindingsTerm left) (bindingsTerm right) arguments _ captured length
    (merge_body_returns state left right)

/-- Recursive callers can supply already captured pattern data without
evaluating its contents a second time. -/
theorem bind_captured_returns (caller : Subst) (state : State) (pattern subject : PatternPlan)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [patternValue pattern.erase, patternValue subject.erase]) :
    PureReturns program caller state (a "gslt:automata:bind" arguments) state
      (encoded (bindingsOptionTerm (matchPattern pattern.erase subject.erase).head?)) := by
  obtain ⟨result, matched, computed⟩ := bind_body_exact state pattern subject
  have chosen : (matchPattern pattern.erase subject.erase).head? = result := by
    rw [matched]
    cases result <;> rfl
  have length : arguments.length = 2 := by
    have := congrArg List.length captured
    simpa using this
  rw [chosen]
  exact helper_call .bind caller state (InferenceCettaWire.encodePattern pattern.erase)
    (InferenceCettaWire.encodePattern subject.erase) arguments _ captured length computed

theorem bind_children_captured_returns (caller : Subst) (state : State)
    (patterns subjects : List PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [patternsValue patterns, patternsValue subjects]) :
    PureReturns program caller state (a "gslt:automata:bind-children" arguments) state
      (encoded (bindingsOptionTerm (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head?)) := by
  obtain ⟨result, matched, computed⟩ := children_body_exact state patterns subjects
  have chosen : (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head? = result := by
    rw [matched]
    cases result <;> rfl
  have length : arguments.length = 2 := by
    have := congrArg List.length captured
    simpa using this
  rw [chosen]
  exact helper_call .children caller state (patternsTerm patterns) (patternsTerm subjects)
    arguments _ captured length computed

/-- Every completed source computation has precisely the canonical binding
answer, the unchanged store, and empty input/output observations. -/
theorem bind_completed_iff (state : State) (pattern subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate []
          (a "gslt:automata:bind" [patternValue pattern.erase, patternValue subject.erase]) } =
      .complete after answers input output) ↔
      after = state ∧
        answers = [encoded (bindingsOptionTerm (matchPattern pattern.erase subject.erase).head?)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (bind_returns state pattern subject)
    after answers input output

/-- Exact observation correspondence in the consolidated PeTTa judgment. -/
theorem bind_derivation_iff (state : State) (pattern subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (a "gslt:automata:bind" [patternValue pattern.erase, patternValue subject.erase]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [encoded (bindingsOptionTerm (matchPattern pattern.erase subject.erase).head?)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (bind_returns state pattern subject)
    after answers input output

theorem bind_children_completed_iff (state : State) (patterns subjects : List PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate []
          (a "gslt:automata:bind-children" [patternsValue patterns, patternsValue subjects]) } =
      .complete after answers input output) ↔
      after = state ∧
        answers = [encoded (bindingsOptionTerm
          (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head?)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (bind_children_returns state patterns subjects)
    after answers input output

theorem bind_children_derivation_iff (state : State) (patterns subjects : List PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (a "gslt:automata:bind-children" [patternsValue patterns, patternsValue subjects]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [encoded (bindingsOptionTerm
          (matchArgs (erasePatterns patterns) (erasePatterns subjects)).head?)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (bind_children_returns state patterns subjects)
    after answers input output

def boundMatchTerm (matched : BoundMatch) : Term :=
  .application "Found" [positionTerm matched.location.position,
    .natural matched.location.occurrence, bindingsTerm matched.bindings]

def matchesTerm (results : List BoundMatch) : Term := encodeList boundMatchTerm results

private abbrev matchesValue (results : List BoundMatch) : Atom := encoded (matchesTerm results)
private abbrev locationsValue (locations : List Location) : Atom := encoded (encodeList locationTerm locations)
private abbrev positionValue (position : Position) : Atom := encoded (positionTerm position)
private abbrev number (value : Nat) : Atom := encoded (.natural value)

private inductive FoldHelper where
  | rows | children

private def FoldHelper.head : FoldHelper → String
  | .rows => "gslt:automata:attempt-rows"
  | .children => "gslt:automata:complete-children"

private def FoldHelper.subjectName : FoldHelper → String
  | .rows => "subject"
  | .children => "subjects"

attribute [local simp] FoldHelper.head FoldHelper.subjectName

private def foldEquation (helper : FoldHelper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

private def foldEnvironment (helper : FoldHelper) (candidates patterns subject path : Term) (next : Nat) : Subst :=
  [("next", number next), ("path", encoded path), (helper.subjectName, encoded subject),
    ("patterns", encoded patterns), ("candidates", encoded candidates)]

private theorem fold_clause (helper : FoldHelper) (candidates patterns subject path : Term) (next : Nat) :
    clauses program helper.head [encoded candidates, encoded patterns, encoded subject, encoded path, number next] =
      [.evaluate (foldEnvironment helper candidates patterns subject path next) (foldEquation helper).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations helper.head).filterMap _ = _
  have unique : equations helper.head = [foldEquation helper] := by cases helper <;> rfl
  have formals : (foldEquation helper).arguments =
      [v "candidates", v "patterns", v helper.subjectName, v "path", v "next"] := by
    cases helper <;> decide +kernel
  rw [unique]
  cases helper <;> simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, foldEnvironment]

private theorem fold_call (helper : FoldHelper) (caller : Subst) (state : State)
    (candidates patterns subject path : Term) (next : Nat) (one two three four index answer : Atom)
    (captured : [one, two, three, four].map (applySubst caller) =
      [encoded candidates, encoded patterns, encoded subject, encoded path])
    (indexComputed : PureReturns program caller state index state (number next))
    (computed : PureReturns program (foldEnvironment helper candidates patterns subject path next) state
      (foldEquation helper).body state answer) :
    PureReturns program caller state (a helper.head [one, two, three, four, index]) state answer := by
  apply PureData.raw_prefix_authored_call_return program caller
    (foldEnvironment helper candidates patterns subject path next) state state state helper.head
    [one, two, three, four] [encoded candidates, encoded patterns, encoded subject, encoded path]
    index (number next) (foldEquation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel) (by cases helper <;> decide) _
    (by simp only [List.length_cons, List.length_nil]; cases helper <;> decide +kernel) captured indexComputed
    (fold_clause helper candidates patterns subject path next) computed
  intro index bounded
  have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
    simp only [List.length_cons, List.length_nil] at bounded
    omega
  rcases small with rfl | rfl | rfl | rfl <;> cases helper <;> decide +kernel

private theorem successor_returns (caller : Subst) (state : State) (next : Nat)
    (captured : applySubst caller (v "next") = number next) :
    PureReturns program caller state (a "+" [v "next", number 1]) state (number (next + 1)) := by
  apply native_binary_call_returns program caller state state state state "+" (v "next") (number 1)
    (number next) (number 1) (number (next + 1))
    (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
  · simpa only [captured] using variable_returns program caller state "next"
  · exact grounded_returns program caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one]
      using StdLib.integer_addition state (next : Int) 1

private theorem positionTerm_injective : Function.Injective positionTerm := by
  intro left right same
  have decoded := congrArg
    (decodeList (fun term => match term with | .natural value => some value | _ => none)) same
  simpa [positionTerm, decodeList_encodeList] using decoded

private theorem locationTerm_injective : Function.Injective locationTerm := by
  intro left right same
  obtain ⟨position, occurrence⟩ := left
  obtain ⟨other, index⟩ := right
  have arguments := (Term.application.inj same).2
  have positions := (List.cons.inj arguments).1
  have indices := (List.cons.inj (List.cons.inj arguments).2).1
  exact congrArg₂ Location.mk (positionTerm_injective positions) (Term.natural.inj indices)

private theorem member_captured_returns (caller : Subst) (state : State) (value : Term)
    (values : List Term) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded value, encoded (encodeList id values)]) :
    PureReturns program caller state (a "gslt:automata:member" arguments) state
      (Effects.boolean (decide (value ∈ values))) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:automata:member"
    [encoded value, encoded (encodeList id values)] arguments _ (by decide +kernel) _ (by decide)
    (by simpa using captured.symm) (MatchAutomataSourceExecution.member_returns state value values)
  intro index bounded
  have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
  rcases small with rfl | rfl <;> decide +kernel

private def rowMatches (candidates : List Location) (patterns : List PatternPlan) (subject : PatternPlan)
    (path : Position) (next : Nat) : List BoundMatch :=
  (patterns.zipIdx next).flatMap fun row =>
    if (⟨path, row.2⟩ : Location) ∈ candidates then
      (matchPattern row.1.erase subject.erase).map fun bindings => ⟨⟨path, row.2⟩, bindings⟩
    else []

private theorem rows_cons (candidates : List Location) (pattern : PatternPlan)
    (patterns : List PatternPlan) (subject : PatternPlan) (path : Position) (next : Nat) :
    rowMatches candidates (pattern :: patterns) subject path next =
      (if (⟨path, next⟩ : Location) ∈ candidates then
        (matchPattern pattern.erase subject.erase).map fun bindings => ⟨⟨path, next⟩, bindings⟩ else []) ++
      rowMatches candidates patterns subject path (next + 1) := by
  simp only [rowMatches, List.zipIdx_cons, List.flatMap_cons]

private def rowsFound : Atom :=
  a "LCons" [a "Found" [v "path", v "next", v "bindings"], v "tail"]
private def rowsResultCases : SpaceSemantics.Cases :=
  [(a "Some" [v "bindings"], rowsFound), (.symbol "None", v "tail")]
private def rowsCons : Atom :=
  a "let" [v "tail",
    a "gslt:automata:attempt-rows" [v "candidates", v "ps", v "subject", v "path",
      a "+" [v "next", number 1]],
    a "if" [a "gslt:automata:member" [a "At" [v "path", v "next"], v "candidates"],
      a "case" [a "gslt:automata:bind" [v "p", v "subject"],
        .expression (rowsResultCases.map fun row => .expression [row.1, row.2])],
      v "tail"]]
private def rowsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "p", v "ps"], rowsCons)]

private theorem rows_shape : (foldEquation .rows).body =
    a "case" [v "patterns", .expression (rowsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem found_template : PureData.Template program rowsFound := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply PureData.Template.constructor "Found" _ (by decide +kernel) (by decide)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .captured _
  · exact .captured _

private theorem rows_body_returns (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan) (path : Position) (next : Nat) :
    PureReturns program
      (foldEnvironment .rows (encodeList locationTerm candidates) (patternsTerm patterns)
        (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) next) state
      (foldEquation .rows).body state (matchesValue (rowMatches candidates patterns subject path next)) := by
  induction patterns generalizing next with
  | nil =>
      let bindings := foldEnvironment .rows (encodeList locationTerm candidates) (patternsTerm [])
        (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) next
      rw [rows_shape]
      apply case_returns program bindings bindings state state state (v "patterns") (.symbol "LNil")
        (.symbol "LNil") (matchesValue (rowMatches candidates [] subject path next))
        _ rowsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, foldEnvironment, patternsTerm, erasePatterns,
          InferenceCettaWire.encodePatterns, applySubst, Subst.lookup, CettaWireAtom.encode]
          using variable_returns program bindings state "patterns"
      · simp [rowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [rowMatches, matchesValue, matchesTerm, encodeList, CettaWireAtom.encode]
          using symbol_returns program bindings state "LNil"
  | cons pattern patterns ih =>
      let bindings := foldEnvironment .rows (encodeList locationTerm candidates) (patternsTerm (pattern :: patterns))
        (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) next
      let selected := ("ps", patternsValue patterns) :: ("p", patternValue pattern.erase) :: bindings
      let tail := rowMatches candidates patterns subject path (next + 1)
      let bound := ("tail", matchesValue tail) :: selected
      have recursive := fold_call .rows selected state (encodeList locationTerm candidates) (patternsTerm patterns)
        (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) (next + 1)
        (v "candidates") (v "ps") (v "subject") (v "path") (a "+" [v "next", number 1])
        (matchesValue tail)
        (by simp [selected, bindings, foldEnvironment, applySubst, Subst.lookup])
        (successor_returns selected state next
          (by simp [selected, bindings, foldEnvironment, applySubst, Subst.lookup])) (ih (next + 1))
      have tested := member_captured_returns bound state (locationTerm ⟨path, next⟩)
        (candidates.map locationTerm) [a "At" [v "path", v "next"], v "candidates"]
        (by simp [bound, selected, bindings, foldEnvironment, applySubst, applySubst.applySubstList,
          Subst.lookup, locationTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, Function.comp_def]; rfl)
      have memberExact : locationTerm ⟨path, next⟩ ∈ candidates.map locationTerm ↔
          (⟨path, next⟩ : Location) ∈ candidates := by
        simp [locationTerm_injective.eq_iff]
      simp only [memberExact] at tested
      rw [rows_shape]
      apply case_returns program bindings selected state state state (v "patterns")
        (patternsValue (pattern :: patterns)) rowsCons
        (matchesValue (rowMatches candidates (pattern :: patterns) subject path next))
        _ rowsCases (read_cases_encoded _) _ _ _
      · simpa [bindings, foldEnvironment, applySubst, Subst.lookup]
          using variable_returns program bindings state "patterns"
      · simp [rowsCases, patternsValue, patternsTerm, erasePatterns, InferenceCettaWire.encodePatterns,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
          Subst.lookup, selected, bindings, foldEnvironment]
      · apply let_returns program selected bound state state state (v "tail")
          (a "gslt:automata:attempt-rows" [v "candidates", v "ps", v "subject", v "path",
            a "+" [v "next", number 1]]) _ (matchesValue tail) _ recursive _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, selected, bindings, foldEnvironment]
        · apply if_returns program bound state state state _ _ _ _ _ tested
          by_cases accepted : (⟨path, next⟩ : Location) ∈ candidates
          · have bindingComputed := bind_captured_returns bound state pattern subject [v "p", v "subject"]
              (by simp [bound, selected, bindings, foldEnvironment, applySubst, Subst.lookup])
            have singleton := (bind_matches_singleton pattern subject).symm
            cases matched : (matchPattern pattern.erase subject.erase).head? with
            | none =>
                simp only [matched, Option.toList_none] at singleton
                have returned : PureReturns program bound state
                    (a "case" [a "gslt:automata:bind" [v "p", v "subject"],
                      .expression (rowsResultCases.map fun row => .expression [row.1, row.2])]) state
                    (matchesValue tail) := by
                  apply case_returns program bound bound state state state _ (.symbol "None") (v "tail")
                    (matchesValue tail) _ rowsResultCases (read_cases_encoded _)
                    (by simpa [matched, bindingsOptionTerm, CettaWireAtom.encode] using bindingComputed) _ _
                  · simp [rowsResultCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
                  · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "tail"
                simpa [accepted, rows_cons, singleton, tail] using returned
            | some found =>
                simp only [matched, Option.toList_some] at singleton
                let checked := ("bindings", bindingsValue found) :: bound
                have returned : PureReturns program bound state
                    (a "case" [a "gslt:automata:bind" [v "p", v "subject"],
                      .expression (rowsResultCases.map fun row => .expression [row.1, row.2])]) state
                    (matchesValue (⟨⟨path, next⟩, found⟩ :: tail)) := by
                  apply case_returns program bound checked state state state _
                    (encoded (bindingsOptionTerm (some found))) rowsFound
                    (matchesValue (⟨⟨path, next⟩, found⟩ :: tail)) _ rowsResultCases (read_cases_encoded _)
                    (by simpa [matched] using bindingComputed) _ _
                  · simp [rowsResultCases, bindingsOptionTerm, CettaWireAtom.encode,
                      CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
                      checked, bound, selected, bindings, foldEnvironment]
                  · simpa [rowsFound, checked, bound, selected, bindings, foldEnvironment,
                      applySubst, applySubst.applySubstList, Subst.lookup, matchesValue,
                      matchesTerm, boundMatchTerm, bindingsValue, encodeList,
                      CettaWireAtom.encode, CettaWireAtom.encodeMany]
                      using PureData.template_return program checked state _ found_template
                simpa [accepted, rows_cons, singleton, tail] using returned
          · simpa [accepted, rows_cons, bound, applySubst, Subst.lookup, tail]
              using variable_returns program bound state "tail"

private def completeAt (candidates : List Location) (patterns : List PatternPlan)
    (subject : PatternPlan) (path : Position) : List BoundMatch :=
  (subterms subject).flatMap fun entry => rowMatches candidates patterns entry.2 (path ++ entry.1) 0

private def completeChildrenAt (candidates : List Location) (patterns subjects : List PatternPlan)
    (path : Position) (next : Nat) : List BoundMatch :=
  (subtermsList next subjects).flatMap fun entry => rowMatches candidates patterns entry.2 (path ++ entry.1) 0

private theorem completeAt_application (candidates : List Location) (patterns : List PatternPlan)
    (head : String) (subjects : List PatternPlan) (path : Position) :
    completeAt candidates patterns (.application head subjects) path =
      rowMatches candidates patterns (.application head subjects) path 0 ++
      completeChildrenAt candidates patterns subjects path 0 := by
  simp [completeAt, subterms, completeChildrenAt]

private theorem completeChildrenAt_cons (candidates : List Location) (patterns : List PatternPlan)
    (subject : PatternPlan) (subjects : List PatternPlan) (path : Position) (next : Nat) :
    completeChildrenAt candidates patterns (subject :: subjects) path next =
      completeAt candidates patterns subject (path ++ [next]) ++
      completeChildrenAt candidates patterns subjects path (next + 1) := by
  simp [completeChildrenAt, subtermsList, List.flatMap_append, List.flatMap_map,
    completeAt, List.append_assoc]

private theorem erasePatterns_map (patterns : List PatternPlan) :
    erasePatterns patterns = patterns.map PatternPlan.erase := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simp [erasePatterns, ih]

private theorem completeAt_root (candidates : List Location) (patterns : List PatternPlan) (subject : PatternPlan) :
    completeAt candidates patterns subject [] =
      MeTTaILSubtermMatchAutomata.complete candidates (erasePatterns patterns) subject := by
  simp only [completeAt, MeTTaILSubtermMatchAutomata.complete, List.nil_append]
  apply List.flatMap_congr
  intro entry _
  simp [rowMatches, erasePatterns_map, List.zipIdx_map, List.flatMap_map]

private theorem append_captured_returns (caller : Subst) (state : State) (left right : List Term)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (encodeList id left), encoded (encodeList id right)]) :
    PureReturns program caller state (a "gslt:automata:append" arguments) state
      (encoded (encodeList id (left ++ right))) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:automata:append"
    [encoded (encodeList id left), encoded (encodeList id right)] arguments _
    (by decide +kernel) _ (by decide) (by simpa using captured.symm)
    (MatchAutomataSourceExecution.append_returns state left right)
  intro index bounded
  have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
  rcases small with rfl | rfl <;> decide +kernel

private theorem appendMatches_returns (caller : Subst) (state : State) (left right : List BoundMatch)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [matchesValue left, matchesValue right]) :
    PureReturns program caller state (a "gslt:automata:append" arguments) state
      (matchesValue (left ++ right)) := by
  have returned := append_captured_returns caller state (left.map boundMatchTerm) (right.map boundMatchTerm)
    arguments (by simpa [matchesValue, matchesTerm, Function.comp_def] using captured)
  rw [← List.map_append] at returned
  simpa only [matchesValue, matchesTerm, encodeList_map, Function.comp_def, id_eq] using returned

private def completeEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:complete")[0]'(by decide +kernel)

private def completeEnvironment (candidates : List Location) (patterns : List PatternPlan)
    (subject : PatternPlan) (path : Position) : Subst :=
  [("path", positionValue path), ("subject", patternValue subject.erase),
    ("patterns", patternsValue patterns), ("candidates", locationsValue candidates)]

private theorem complete_clause (candidates : List Location) (patterns : List PatternPlan)
    (subject : PatternPlan) (path : Position) :
    clauses program "gslt:automata:complete"
      [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue path] =
      [.evaluate (completeEnvironment candidates patterns subject path) completeEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations "gslt:automata:complete").filterMap _ = _
  rw [show equations "gslt:automata:complete" = [completeEquation] from rfl]
  have formals : completeEquation.arguments = [v "candidates", v "patterns", v "subject", v "path"] := by
    decide +kernel
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, completeEnvironment]

private theorem complete_call (caller : Subst) (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan) (path : Position)
    (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue path])
    (computed : PureReturns program (completeEnvironment candidates patterns subject path) state
      completeEquation.body state (matchesValue (completeAt candidates patterns subject path))) :
    PureReturns program caller state (a "gslt:automata:complete" arguments) state
      (matchesValue (completeAt candidates patterns subject path)) := by
  apply PureData.raw_authored_call_return program caller (completeEnvironment candidates patterns subject path)
    state state "gslt:automata:complete" arguments completeEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ computed
  · intro index bounded
    have length : arguments.length = 4 := by simpa using congrArg List.length captured
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases small with rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured]
    exact complete_clause candidates patterns subject path

private def completeApplication : Atom :=
  a "let" [v "below",
    a "gslt:automata:complete-children" [v "candidates", v "patterns", v "arguments", v "path", number 0],
    a "gslt:automata:append" [v "here", v "below"]]
private def completeCases : SpaceSemantics.Cases :=
  [(a "PApp" [v "head", v "arguments"], completeApplication), (v "leaf", v "here")]
private def completeContinuation : Atom :=
  a "case" [v "subject", .expression (completeCases.map fun row => .expression [row.1, row.2])]

private theorem complete_shape : completeEquation.body =
    a "let" [v "here", a "gslt:automata:attempt-rows"
      [v "candidates", v "patterns", v "subject", v "path", number 0], completeContinuation] := by
  decide +kernel

private def completeChildrenPairs : List Atom :=
  [.expression [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]]],
    .expression [v "head", a "gslt:automata:complete" [v "candidates", v "patterns", v "s", v "child-path"]],
    .expression [v "tail", a "gslt:automata:complete-children"
      [v "candidates", v "patterns", v "ss", v "path", a "+" [v "next", number 1]]]]
private def completeChildrenCons : Atom :=
  a "let*" [.expression completeChildrenPairs, a "gslt:automata:append" [v "head", v "tail"]]
private def completeChildrenCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "s", v "ss"], completeChildrenCons)]

private theorem completeChildren_shape : (foldEquation .children).body =
    a "case" [v "subjects", .expression (completeChildrenCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

mutual
  private theorem complete_body_returns (state : State) (candidates : List Location)
      (patterns : List PatternPlan) (subject : PatternPlan) (path : Position) :
      PureReturns program (completeEnvironment candidates patterns subject path) state
        completeEquation.body state (matchesValue (completeAt candidates patterns subject path)) := by
    let bindings := completeEnvironment candidates patterns subject path
    let here := rowMatches candidates patterns subject path 0
    let bound := ("here", matchesValue here) :: bindings
    have hereComputed := fold_call .rows bindings state (encodeList locationTerm candidates) (patternsTerm patterns)
      (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) 0
      (v "candidates") (v "patterns") (v "subject") (v "path") (number 0) (matchesValue here)
      (by simp [bindings, completeEnvironment, applySubst, Subst.lookup])
      (grounded_returns program bindings state (.int 0))
      (rows_body_returns state candidates patterns subject path 0)
    rw [complete_shape]
    apply let_returns program bindings bound state state state (v "here")
      (a "gslt:automata:attempt-rows" [v "candidates", v "patterns", v "subject", v "path", number 0])
      completeContinuation (matchesValue here) _ hereComputed _ _
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, bindings, completeEnvironment]
    · cases subject with
      | metavariable name =>
          let selected := ("leaf", patternValue (.fvar name)) :: bound
          apply case_returns program bound selected state state state (v "subject")
            (patternValue (.fvar name)) (v "here")
            (matchesValue (completeAt candidates patterns (.metavariable name) path))
            _ completeCases (read_cases_encoded _) _ _ _
          · simpa [bound, bindings, completeEnvironment, PatternPlan.erase, applySubst, Subst.lookup]
              using variable_returns program bound state "subject"
          · simp [completeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
              bound, bindings, completeEnvironment]
          · simpa [selected, bound, applySubst, Subst.lookup, here, completeAt, subterms]
              using variable_returns program selected state "here"
      | bound index =>
          let selected := ("leaf", patternValue (.bvar index)) :: bound
          apply case_returns program bound selected state state state (v "subject")
            (patternValue (.bvar index)) (v "here")
            (matchesValue (completeAt candidates patterns (.bound index) path))
            _ completeCases (read_cases_encoded _) _ _ _
          · simpa [bound, bindings, completeEnvironment, PatternPlan.erase, applySubst, Subst.lookup]
              using variable_returns program bound state "subject"
          · simp [completeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
              bound, bindings, completeEnvironment]
          · simpa [selected, bound, applySubst, Subst.lookup, here, completeAt, subterms]
              using variable_returns program selected state "here"
      | application head subjects =>
          let selected := ("arguments", patternsValue subjects) :: ("head", encoded (.string head)) :: bound
          let below := completeChildrenAt candidates patterns subjects path 0
          let finished := ("below", matchesValue below) :: selected
          have belowComputed := fold_call .children selected state (encodeList locationTerm candidates)
            (patternsTerm patterns) (patternsTerm subjects) (positionTerm path) 0
            (v "candidates") (v "patterns") (v "arguments") (v "path") (number 0) (matchesValue below)
            (by simp [selected, bound, bindings, completeEnvironment, applySubst, Subst.lookup])
            (grounded_returns program selected state (.int 0))
            (completeChildren_body_returns state candidates patterns subjects path 0)
          apply case_returns program bound selected state state state (v "subject")
            (patternValue (.apply head (erasePatterns subjects))) completeApplication
            (matchesValue (completeAt candidates patterns (.application head subjects) path))
            _ completeCases (read_cases_encoded _) _ _ _
          · simpa [bound, bindings, completeEnvironment, PatternPlan.erase, applySubst, Subst.lookup]
              using variable_returns program bound state "subject"
          · simp [completeCases, InferenceCettaWire.encodePattern, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
              bound, bindings, completeEnvironment]
          · apply let_returns program selected finished state state state (v "below")
              (a "gslt:automata:complete-children"
                [v "candidates", v "patterns", v "arguments", v "path", number 0])
              (a "gslt:automata:append" [v "here", v "below"]) (matchesValue below) _ belowComputed _ _
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, finished, selected,
                bound, bindings, completeEnvironment]
            · have returned := appendMatches_returns finished state here below [v "here", v "below"]
                (by simp [finished, selected, bound, applySubst, Subst.lookup])
              simpa only [completeAt_application, here, below] using returned
  termination_by 2 * subject.work
  decreasing_by simp [PatternPlan.work]; omega

  private theorem completeChildren_body_returns (state : State) (candidates : List Location)
      (patterns subjects : List PatternPlan) (path : Position) (next : Nat) :
      PureReturns program
        (foldEnvironment .children (encodeList locationTerm candidates) (patternsTerm patterns)
          (patternsTerm subjects) (positionTerm path) next) state
        (foldEquation .children).body state (matchesValue (completeChildrenAt candidates patterns subjects path next)) := by
    let bindings := foldEnvironment .children (encodeList locationTerm candidates) (patternsTerm patterns)
      (patternsTerm subjects) (positionTerm path) next
    rw [completeChildren_shape]
    cases subjects with
    | nil =>
        apply case_returns program bindings bindings state state state (v "subjects") (.symbol "LNil")
          (.symbol "LNil") (matchesValue (completeChildrenAt candidates patterns [] path next))
          _ completeChildrenCases (read_cases_encoded _) _ _ _
        · simpa [bindings, foldEnvironment, patternsTerm, erasePatterns,
            InferenceCettaWire.encodePatterns, applySubst, Subst.lookup, CettaWireAtom.encode]
            using variable_returns program bindings state "subjects"
        · simp [completeChildrenCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
        · simpa [completeChildrenAt, subtermsList, matchesValue, matchesTerm, encodeList, CettaWireAtom.encode]
            using symbol_returns program bindings state "LNil"
    | cons subject subjects =>
        let selected := ("ss", patternsValue subjects) :: ("s", patternValue subject.erase) :: bindings
        let childPath := path ++ [next]
        let pathBound := ("child-path", positionValue childPath) :: selected
        let head := completeAt candidates patterns subject childPath
        let headBound := ("head", matchesValue head) :: pathBound
        let tail := completeChildrenAt candidates patterns subjects path (next + 1)
        let tailBound := ("tail", matchesValue tail) :: headBound
        have pathComputed : PureReturns program selected state
            (a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]]) state
            (positionValue childPath) := by
          have returned := append_captured_returns selected state (path.map Term.natural) [Term.natural next]
            [v "path", a "LCons" [v "next", .symbol "LNil"]]
            (by simp [selected, bindings, foldEnvironment, applySubst, applySubst.applySubstList,
              Subst.lookup, positionTerm, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              Function.comp_def])
          have values : path.map Term.natural ++ [Term.natural next] = childPath.map Term.natural := by
            simp [childPath]
          rw [values] at returned
          simpa [positionValue, positionTerm, Function.comp_def] using returned
        have headComputed := complete_call pathBound state candidates patterns subject childPath
          [v "candidates", v "patterns", v "s", v "child-path"]
          (by simp [pathBound, selected, bindings, foldEnvironment, applySubst, Subst.lookup])
          (complete_body_returns state candidates patterns subject childPath)
        have tailComputed := fold_call .children headBound state (encodeList locationTerm candidates)
          (patternsTerm patterns) (patternsTerm subjects) (positionTerm path) (next + 1)
          (v "candidates") (v "patterns") (v "ss") (v "path") (a "+" [v "next", number 1])
          (matchesValue tail)
          (by simp [headBound, pathBound, selected, bindings, foldEnvironment, applySubst, Subst.lookup])
          (successor_returns headBound state next
            (by simp [headBound, pathBound, selected, bindings, foldEnvironment, applySubst, Subst.lookup]))
          (completeChildren_body_returns state candidates patterns subjects path (next + 1))
        apply case_returns program bindings selected state state state (v "subjects")
          (patternsValue (subject :: subjects)) completeChildrenCons
          (matchesValue (completeChildrenAt candidates patterns (subject :: subjects) path next))
          _ completeChildrenCases (read_cases_encoded _) _ _ _
        · simpa [bindings, foldEnvironment, applySubst, Subst.lookup]
            using variable_returns program bindings state "subjects"
        · simp [completeChildrenCases, patternsValue, patternsTerm, erasePatterns,
            InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, selected, bindings, foldEnvironment]
        · apply let_star_returns program selected state state completeChildrenPairs _
            (a "let" [v "child-path", a "gslt:automata:append" [v "path", a "LCons" [v "next", .symbol "LNil"]],
              a "let" [v "head", a "gslt:automata:complete" [v "candidates", v "patterns", v "s", v "child-path"],
                a "let" [v "tail", a "gslt:automata:complete-children"
                  [v "candidates", v "patterns", v "ss", v "path", a "+" [v "next", number 1]],
                  a "gslt:automata:append" [v "head", v "tail"]]]]) _ (by rfl)
          apply let_returns program selected pathBound state state state (v "child-path") _ _
            (positionValue childPath) _ pathComputed
          · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, pathBound, selected, bindings, foldEnvironment]
          · apply let_returns program pathBound headBound state state state (v "head") _ _
              (matchesValue head) _ headComputed
            · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, headBound,
                pathBound, selected, bindings, foldEnvironment]
            · apply let_returns program headBound tailBound state state state (v "tail") _ _
                (matchesValue tail) _ tailComputed
              · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound,
                  headBound, pathBound, selected, bindings, foldEnvironment]
              · have returned := appendMatches_returns tailBound state head tail [v "head", v "tail"]
                  (by simp [tailBound, headBound, applySubst, Subst.lookup])
                simpa only [completeChildrenAt_cons, head, tail, childPath] using returned
  termination_by 2 * patternPlansWork subjects + 1
  decreasing_by
    all_goals
      have positive := PatternPlan.work_pos subject
      rw [patternPlansWork]
      omega
end

/-- Row completion keeps the supplied occurrence offset and candidate filter.
It invokes the canonical matcher for each admitted row in authored order. -/
theorem attempt_rows_returns (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan) (path : Position) (next : Nat) :
    PureReturns program [] state
      (a "gslt:automata:attempt-rows"
        [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue path, number next])
      state (matchesValue ((patterns.zipIdx next).flatMap fun row =>
        if (⟨path, row.2⟩ : Location) ∈ candidates then
          (matchPattern row.1.erase subject.erase).map fun bindings => ⟨⟨path, row.2⟩, bindings⟩
        else [])) := by
  exact fold_call .rows [] state (encodeList locationTerm candidates) (patternsTerm patterns)
    (InferenceCettaWire.encodePattern subject.erase) (positionTerm path) next
    (locationsValue candidates) (patternsValue patterns) (patternValue subject.erase)
    (positionValue path) (number next) _ (by simp)
    (grounded_returns program [] state (.int next)) (rows_body_returns state candidates patterns subject path next)

/-- The actual source completion pass agrees with the independent canonical
subterm completion, retaining locations and exact ordered bindings. -/
theorem complete_returns (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:complete"
        [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue []]) state
      (matchesValue (MeTTaILSubtermMatchAutomata.complete candidates (erasePatterns patterns) subject)) := by
  rw [← completeAt_root]
  exact complete_call [] state candidates patterns subject [] _ (by simp)
    (complete_body_returns state candidates patterns subject [])

theorem complete_captured_returns (caller : Subst) (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue []]) :
    PureReturns program caller state (a "gslt:automata:complete" arguments) state
      (matchesValue (MeTTaILSubtermMatchAutomata.complete candidates (erasePatterns patterns) subject)) := by
  rw [← completeAt_root]
  exact complete_call caller state candidates patterns subject [] arguments captured
    (complete_body_returns state candidates patterns subject [])

theorem complete_completed_iff (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate []
          (a "gslt:automata:complete"
            [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue []]) } =
      .complete after answers input output) ↔
      after = state ∧
        answers = [matchesValue (MeTTaILSubtermMatchAutomata.complete candidates (erasePatterns patterns) subject)] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (complete_returns state candidates patterns subject)
    after answers input output

/-- Exact completion observations in the consolidated PeTTa judgment. -/
theorem complete_derivation_iff (state : State) (candidates : List Location)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate []
          (a "gslt:automata:complete"
            [locationsValue candidates, patternsValue patterns, patternValue subject.erase, positionValue []]) }
      (.complete after answers input output) ↔
      after = state ∧
        answers = [matchesValue (MeTTaILSubtermMatchAutomata.complete candidates (erasePatterns patterns) subject)] ∧
        input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (complete_returns state candidates patterns subject)
    after answers input output

section Controls

private def repeatedPattern : PatternPlan :=
  .application "Pair" [.metavariable "x", .metavariable "x"]

private def repeatedSubject : PatternPlan :=
  .application "Pair" [.application "Value" [], .application "Value" []]

private def conflictingSubject : PatternPlan :=
  .application "Pair" [.application "Value" [], .application "Other" []]

/-- Repeating a consistent payload retains one canonical binding. -/
theorem repeated_variable_accepts (state : State) :
    PureReturns program [] state
      (a "gslt:automata:bind" [patternValue repeatedPattern.erase, patternValue repeatedSubject.erase]) state
      (encoded (bindingsOptionTerm (some [("x", .apply "Value" [])]))) := by
  have expected : (matchPattern repeatedPattern.erase repeatedSubject.erase).head? =
      some [("x", .apply "Value" [])] := by decide +kernel
  simpa only [expected] using bind_returns state repeatedPattern repeatedSubject

/-- Structural wildcard success does not authorize inconsistent bindings. -/
theorem repeated_variable_refuses (state : State) :
    PureReturns program [] state
      (a "gslt:automata:bind" [patternValue repeatedPattern.erase, patternValue conflictingSubject.erase]) state
      (encoded (bindingsOptionTerm none)) := by
  have expected : (matchPattern repeatedPattern.erase conflictingSubject.erase).head? = none := by decide +kernel
  simpa only [expected] using bind_returns state repeatedPattern conflictingSubject

/-- A captured payload that is itself an authored call remains literal data. -/
theorem opaque_payload_lookup (state : State) :
    PureReturns program [] state
      (a "gslt:automata:binding" [encoded (.string "payload"),
        encoded (payloadBindingsTerm [("payload", .application "+" [.natural 2, .natural 3])])]) state
      (encoded (.application "Some" [.application "+" [.natural 2, .natural 3]])) := by
  simpa [payloadLookup, payloadOptionTerm] using payload_binding_returns state "payload"
    [("payload", .application "+" [.natural 2, .natural 3])]

/-- A later equal-name row cannot replace the first stored payload. -/
theorem duplicate_payload_keeps_first (state : State) :
    PureReturns program [] state
      (a "gslt:automata:binding" [encoded (.string "payload"),
        encoded (payloadBindingsTerm [("payload", .symbol "first"), ("payload", .symbol "later")])]) state
      (encoded (.application "Some" [.symbol "first"])) := by
  simpa [payloadLookup, payloadOptionTerm] using payload_binding_returns state "payload"
    [("payload", .symbol "first"), ("payload", .symbol "later")]

theorem missing_payload_lookup (state : State) :
    PureReturns program [] state
      (a "gslt:automata:binding" [encoded (.string "missing"),
        encoded (payloadBindingsTerm [("payload", .symbol "present")])]) state
      (.symbol "None") := by
  simpa [payloadLookup, payloadOptionTerm, CettaWireAtom.encode] using payload_binding_returns state "missing"
    [("payload", .symbol "present")]

end Controls

#print axioms patternOptionTerm_injective
#print axioms payload_binding_returns
#print axioms payload_binding_captured_returns
#print axioms binding_returns
#print axioms merge_returns
#print axioms bind_returns
#print axioms bind_children_returns
#print axioms bind_derivation_iff
#print axioms bind_children_derivation_iff
#print axioms attempt_rows_returns
#print axioms complete_returns
#print axioms complete_derivation_iff
#print axioms repeated_variable_accepts
#print axioms repeated_variable_refuses
#print axioms opaque_payload_lookup
#print axioms duplicate_payload_keeps_first
#print axioms missing_payload_lookup

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution
