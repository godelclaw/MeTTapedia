import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationRunExecution
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec

/-!
# Original MMB constructor admission and exhaustive refusals

Actual resolver lookup, declaration selection and ordered stack consumption
are qualified against the unchanged quoted binary proof source. Numeric term
identities and list-shaped declaration argument payloads are explicit source
admission conditions. Complete expression fields and chronological authority
are earned from original construction, including unused stack entries and
repeated children. Refusal returns one None answer and does not execute the
remaining command suffix. Malformed raw command shapes, nonnumeric resolver
values and non-list argument payloads retain their separate source behavior.

Theorem application, conversion continuations and kernel typing remain
independent obligations; constructor allocation alone supplies none of them.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBConstructorExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom applySubst_nil)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue provedValue)
open MMBTheoremSignatureExecution (DeclarationShape ArgumentListRows)
open MMBAllocationExecution
open MMBAllocationRunExecution (StateAuthority)
open Kernel (Preterm)
abbrev program := MMBAllocationExecution.program
private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD ⟨"", [], .symbol "None"⟩
private def termEquation := sourceEquation "mm0:mmb:proof-term"
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def termCase := match termEquation.body with | .expression [_, _, body] => body | _ => .symbol "None"
private def termCases := casesOf termCase
private def termFound := (termCases[0]'(by decide)).2
private def termPopCases := casesOf termFound
private def termPopped := (termPopCases[0]'(by decide)).2
private def termValueCases := casesOf termPopped
private def termValues := (termValueCases[0]'(by decide)).2
private def termResult := match termValues with | .expression [_, _, body] => body | _ => .symbol "None"
private def termEnvironment (resolver tableSorts tableTheorems : Atom) (tableTerms : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) : Subst :=
  [("save", boolean save), ("binary", natural binary), ("saved", listValue saved), ("hyps", listValue hypotheses),
    ("dummies", listValue dummies), ("heap", listValue heap), ("stack", listValue stack),
    ("count", natural count), ("arity", natural arity), ("next", natural next),
    ("theorems", tableTheorems), ("terms", listValue tableTerms), ("sorts", tableSorts), ("resolver", resolver)]
private theorem term_unique : program.equations.filter (·.head == "mm0:mmb:proof-term") = [termEquation] := by decide +kernel
private theorem term_formals : termEquation.arguments =
    [.var "resolver", .expression [.symbol "MM0:MMBTables", .var "sorts", .var "terms", .var "theorems"],
      .expression [.symbol "MM0:MMBPState", .var "next", .var "arity", .var "count", .var "stack", .var "heap",
        .var "dummies", .var "hyps", .var "saved"], .var "binary", .var "save"] := by decide
private theorem term_shape : termEquation.body =
    .expression [.symbol "let*", .expression [
      .expression [.var "found", .expression [.symbol "mm0:mmu:term", .var "resolver", .var "binary"]],
      .expression [.var "entry", .expression [.symbol "mm0:data-at", .var "terms", .var "binary"]]], termCase] := by decide
private theorem term_case_shape : termCase =
    .expression [.symbol "case", .expression [.var "found", .var "entry"],
      .expression (termCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_cases_shape : termCases =
    [(.expression [.expression [.symbol "Some", .var "id"],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMBTerm", .var "sort",
        .expression [.symbol "MM0:L", .var "args"], .var "ret", .var "value"]]], termFound),
      (.var "bad", .symbol "None")] := by decide
private theorem term_found_shape : termFound =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:pop-many", .symbol "MM0:MMBExpressions",
      .expression [.symbol "size-atom", .var "args"], .var "stack"],
      .expression (termPopCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem term_pop_cases_shape : termPopCases =
    [(.expression [.symbol "Some", .expression [.symbol "MM0:MMBPopped", .var "arguments", .var "rest"]],
      termPopped), (.var "bad", .symbol "None")] := by decide
private theorem term_clause (resolver tableSorts tableTheorems : Atom) (tableTerms : List Atom)
    (next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (binary : Nat) (save : Bool) :
    clauses program "mm0:mmb:proof-term"
      [resolver, .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems],
        stateValue next arity count stack heap dummies hypotheses saved, natural binary, boolean save] =
      [.evaluate (termEnvironment resolver tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
        termEquation.body] := by
  rw [clauses_use_only_the_named_equations, term_unique]
  simp [term_formals, termEnvironment, stateValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem computed_pop_returns (bindings : Subst) (state : State) (formalArguments stack : List Atom) (result : Option (List Atom × List Atom))
    (argsCaptured : applySubst bindings (.var "args") = .expression formalArguments)
    (stackCaptured : applySubst bindings (.var "stack") = listValue stack)
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:pop-many", .symbol "MM0:MMBExpressions",
      .expression [.symbol "size-atom", .var "args"], .var "stack"]) state
      (MMBTheoremCommandExecution.poppedValue result) := by
  let prior : Subst := [("kind", .symbol "MM0:MMBExpressions"), ("number", natural formalArguments.length), ("items", listValue stack)]
  have original := MMBTheoremCommandExecution.pop_many_returns prior state .expressions formalArguments.length stack
    result "kind" "number" "items" rfl rfl rfl popped
  have finished := captured_function_arguments_returns program prior bindings state state "mm0:mmb:pop-many"
    [.var "kind", .var "number", .var "items"] 3 _ (by decide +kernel) (by decide)
    (by intro offset argument selected; have bound := (getElem?_eq_some_iff.mp selected).choose
        have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 := by simp only [List.length_cons, List.length_nil] at bound; omega
        rcases positions with rfl | rfl | rfl <;> simp at selected <;> subst argument <;> exact Or.inr rfl) original
  apply call_returns program bindings state state "mm0:mmb:pop-many" _ _ (by decide +kernel) _ (by decide)
  apply raw_argument_answers program bindings state state "mm0:mmb:pop-many" (.symbol "MM0:MMBExpressions")
    [.expression [.symbol "size-atom", .var "args"], .var "stack"] [] 0 [_] (by decide +kernel)
  apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:pop-many")
    (.expression [.symbol "size-atom", .var "args"]) (natural formalArguments.length) _ _ _ 1 (by decide +kernel)
  · apply native_variable_call_returns program bindings state state "size-atom" ["args"]
      (natural formalArguments.length) (by decide) (by decide) _ (by decide)
    change StdLib.apply state "size-atom" [applySubst bindings (.var "args")] = .ok (state, [natural formalArguments.length])
    rw [argsCaptured]
    rfl
  · apply variable_arguments_return program bindings state state (.function "mm0:mmb:pop-many")
      ["stack"] [.symbol "MM0:MMBExpressions", natural formalArguments.length] 2 _
    change (theory program).MultiStep
      { state, control := .arguments bindings (.function "mm0:mmb:pop-many") [] [.symbol "MM0:MMBExpressions", natural formalArguments.length, applySubst bindings (.var "stack")] 3 }
      (Eval.finished state [MMBTheoremCommandExecution.poppedValue result] [] [])
    rw [stackCaptured]
    simpa [prior, applySubst, Subst.lookup] using finished


private def declarationPattern : Atom :=
  .expression [.symbol "MM0:MMBTerm", .var "sort",
    .expression [.symbol "MM0:L", .var "args"], .var "ret", .var "value"]

private inductive StructuralPattern : Atom → Prop where
  | var (name : String) : StructuralPattern (.var name)
  | symbol (name : String) : StructuralPattern (.symbol name)
  | grounded (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) : StructuralPattern (.grounded value)
  | expression (patterns : List Atom)
      (notCons : ∀ first rest, patterns ≠ [.symbol "cons", first, rest])
      (members : ∀ pattern ∈ patterns, StructuralPattern pattern) : StructuralPattern (.expression patterns)

private theorem StructuralPattern.matches {pattern : Atom} (structural : StructuralPattern pattern)
    (bindings : Subst) (value : Atom) :
    SpaceSemantics.matchValue bindings pattern value = matchAtom bindings pattern value := by
  induction structural generalizing bindings value with
  | var name => simp only [SpaceSemantics.matchValue]
  | symbol name => simp only [SpaceSemantics.matchValue]
  | grounded ground => simp only [SpaceSemantics.matchValue]
  | expression patterns notCons members ih =>
      have lists (values : List Atom) : SpaceSemantics.matchValue.matchValues bindings patterns values =
          matchAtom.matchAtomList bindings patterns values := by
        clear notCons members
        induction patterns generalizing bindings values with
        | nil => cases values <;> simp only [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
        | cons first rest tail =>
            cases values with
            | nil => simp only [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList]
            | cons value values =>
                simp only [SpaceSemantics.matchValue.matchValues, matchAtom.matchAtomList,
                  ih first List.mem_cons_self bindings value]
                cases captured : matchAtom bindings first value with
                | none => rfl
                | some middle =>
                    exact tail (fun item member => ih item (List.mem_cons_of_mem _ member)) middle values
      cases value with
      | expression values =>
          rw [SpaceSemantics.matchValue_expression_of_not_cons bindings patterns values notCons, lists]
          rfl
      | var name | symbol name | grounded ground =>
          unfold SpaceSemantics.matchValue
          split <;> simp_all [matchAtom]

private theorem declaration_structural : StructuralPattern declarationPattern := by
  apply StructuralPattern.expression
  · intro first rest same; simp at same
  · intro pattern member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact .symbol _
    · exact .var _
    · apply StructuralPattern.expression
      · intro first rest same; simp at same
      · intro item member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .symbol _
        · exact .var _
    · exact .var _
    · exact .var _

private theorem declaration_relation_shape {bindings bound : Subst} {entry : Atom}
    (relation : Mettapedia.Languages.ProcessCalculi.MORK.MatchAtomRel bindings declarationPattern entry bound) :
    DeclarationShape entry := by
  cases relation with
  | expr_cons head tail =>
    cases head
    cases tail with
    | expr_cons sortMatched tail =>
      cases tail with
      | expr_cons wrapperMatched tail =>
        cases wrapperMatched with
        | expr_cons tag tailArgs =>
          cases tag
          cases tailArgs with
          | expr_cons argsMatched emptyArgs =>
            cases emptyArgs
            cases tail with
            | expr_cons retMatched tail =>
              cases tail with
              | expr_cons valueMatched empty =>
                cases empty
                exact ⟨_, _, _, _, rfl⟩


private theorem declaration_match_shape {bindings bound : Subst} {entry : Atom}
    (matched : SpaceSemantics.matchValue bindings declarationPattern entry = some bound) :
    DeclarationShape entry := by
  rw [declaration_structural.matches] at matched
  exact declaration_relation_shape (Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound matched)

/-- Every malformed declaration constructor skips the original success row. -/
theorem declaration_match_refused (bindings : Subst) (entry : Atom)
    (malformed : ¬ DeclarationShape entry) :
    SpaceSemantics.matchValue bindings declarationPattern entry = none := by
  cases matched : SpaceSemantics.matchValue bindings declarationPattern entry with
  | none => rfl
  | some bound => exact False.elim (malformed (declaration_match_shape matched))


private def termPattern := (termCases[0]'(by decide)).1
private theorem termPattern_structural : StructuralPattern termPattern := by
  rw [show termPattern = .expression [
    .expression [.symbol "Some", .var "id"],
    .expression [.symbol "Some", declarationPattern]] from by decide]
  apply StructuralPattern.expression
  · intro first rest same; simp at same
  · intro pattern member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply StructuralPattern.expression
      · intro first rest same; simp at same
      · intro item member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .symbol _
        · exact .var _
    · apply StructuralPattern.expression
      · intro first rest same; simp at same
      · intro item member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .symbol _
        · exact declaration_structural

private theorem termPattern_match_fields {bindings bound : Subst} (found entry : Option Atom)
    (matched : SpaceSemantics.matchValue bindings termPattern
      (.expression [optionValue found, optionValue entry]) = some bound) :
    ∃ identifier declaration, found = some identifier ∧ entry = some declaration ∧ DeclarationShape declaration := by
  rw [termPattern_structural.matches] at matched
  have relation := Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound matched
  rw [show termPattern = .expression [
    .expression [.symbol "Some", .var "id"],
    .expression [.symbol "Some", declarationPattern]] from by decide] at relation
  cases relation with
  | expr_cons foundRelation tail =>
    cases tail with
    | expr_cons entryRelation empty =>
      cases found with
      | none => cases foundRelation
      | some identifier =>
        cases entry with
        | none => cases entryRelation
        | some declaration =>
          cases entryRelation with
          | expr_cons tag tail =>
            cases tail with
            | expr_cons declarationRelation empty =>
              exact ⟨identifier, declaration, rfl, rfl, declaration_relation_shape declarationRelation⟩

/-- These are the original lookup, row-shape and ordered pop refusals. They
contain no premise about the result of the proof-term operation. -/
inductive Refusal (terms : List MMUResolution.Binding) (tableTerms : List Atom)
    (binary : Nat) (stack : List Atom) : Prop where
  | missingName (absent : MMUResolution.lookup terms (natural binary) = none)
  | missingDeclaration (absent : tableTerms[binary]? = none)
  | malformedDeclaration {entry : Atom} (declared : tableTerms[binary]? = some entry)
      (malformed : ¬ DeclarationShape entry)
  | pop {identifier sort ret value : Atom} {formalArguments : List Atom}
      (resolved : MMUResolution.lookup terms (natural binary) = some identifier)
      (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
      (refused : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack none)

private theorem lookup_prefix_returns (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images tableSorts tableTheorems : Atom) (tableTerms : List Atom)
    (binary next arity count : Nat) (stack heap dummies hypotheses saved : List Atom) (save : Bool) (answer : Atom)
    (continuation : PureReturns program
      (("entry", optionValue (tableTerms[binary]?)) ::
       ("found", optionValue (MMUResolution.lookup terms (natural binary))) ::
       termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
         tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
      state termCase state answer) :
    PureReturns program
      (termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
      state termEquation.body state answer := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := termEnvironment resolver tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save
  let found := ("found", optionValue (MMUResolution.lookup terms (natural binary))) :: bindings
  let entered := ("entry", optionValue (tableTerms[binary]?)) :: found
  rw [term_shape]
  apply let_star_returns program bindings state state _ _ _ _ rfl
  apply let_returns program bindings found state state state (.var "found") _ _ (optionValue (MMUResolution.lookup terms (natural binary))) _
  · simpa only [MMBTheoremSignatureExecution.ResolverField.head, MMBTheoremSignatureExecution.ResolverField.entries] using
      MMBTheoremSignatureExecution.resolver_returns .term bindings state published sorts terms theorems
        nextSort nextTerm nextTheorem images (natural binary) "resolver" "binary" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, found, bindings, termEnvironment, Subst.lookup]
  · apply let_returns program found entered state state state (.var "entry") _ _ (optionValue (tableTerms[binary]?)) _
    · exact MMBProofRunExecution.checker_returns (by decide +kernel)
        (ListAccess.data_at_list_returns found state tableTerms binary "terms" "binary" rfl rfl)
    · simp [SpaceSemantics.matchValue, matchAtom, entered, found, bindings, termEnvironment, Subst.lookup]
    · exact continuation

private theorem refused_case_returns (state : State) (bindings : Subst) (found entry : Option Atom)
    (foundCaptured : applySubst bindings (.var "found") = optionValue found)
    (entryCaptured : applySubst bindings (.var "entry") = optionValue entry)
    (badFresh : bindings.lookup "bad" = none)
    (rejected : SpaceSemantics.matchValue bindings termPattern (.expression [optionValue found, optionValue entry]) = none) :
    PureReturns program bindings state termCase state (.symbol "None") := by
  let denied := ("bad", .expression [optionValue found, optionValue entry]) :: bindings
  rw [term_case_shape]
  apply case_returns program bindings denied state state state (.expression [.var "found", .var "entry"])
    (.expression [optionValue found, optionValue entry]) (.symbol "None") _ _
    termCases (read_cases_encoded termCases)
  · simpa only [List.map_cons, List.map_nil, foundCaptured, entryCaptured] using
      tuple_variables_return program bindings state ["found", "entry"]
  · rw [show termCases = [(termPattern, termFound), (.var "bad", .symbol "None")] from by decide]
    simp only [SpaceSemantics.selectCase, rejected]
    simp [SpaceSemantics.matchValue, matchAtom, badFresh, denied]
  · exact symbol_returns program denied state "None"

private theorem Refusal.body_returns {terms : List MMUResolution.Binding} {tableTerms stack : List Atom} {binary : Nat}
    (refusal : Refusal terms tableTerms binary stack) (state : State) (published : Atom)
    (sorts theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images tableSorts tableTheorems : Atom) (next arity count : Nat) (heap dummies hypotheses saved : List Atom) (save : Bool) :
    PureReturns program
      (termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
        tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
      state termEquation.body state (.symbol "None") := by
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let bindings := termEnvironment resolver tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save
  let entered := ("entry", optionValue (tableTerms[binary]?)) ::
    ("found", optionValue (MMUResolution.lookup terms (natural binary))) :: bindings
  apply lookup_prefix_returns state published sorts terms theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
    tableTerms binary next arity count stack heap dummies hypotheses saved save (.symbol "None")
  cases refusal with
  | missingName absent =>
      apply refused_case_returns state entered _ _ rfl rfl rfl
      cases matched : SpaceSemantics.matchValue entered termPattern
        (.expression [optionValue (MMUResolution.lookup terms (natural binary)), optionValue (tableTerms[binary]?)]) with
      | none => rfl
      | some bound =>
          obtain ⟨id, entry, found, _, _⟩ := termPattern_match_fields _ _ matched
          simp [absent] at found
  | missingDeclaration absent =>
      apply refused_case_returns state entered _ _ rfl rfl rfl
      cases matched : SpaceSemantics.matchValue entered termPattern
        (.expression [optionValue (MMUResolution.lookup terms (natural binary)), optionValue (tableTerms[binary]?)]) with
      | none => rfl
      | some bound =>
          obtain ⟨id, entry, _, found, _⟩ := termPattern_match_fields _ _ matched
          simp [absent] at found
  | @malformedDeclaration entry declared malformed =>
      apply refused_case_returns state entered _ _ rfl rfl rfl
      cases matched : SpaceSemantics.matchValue entered termPattern
        (.expression [optionValue (MMUResolution.lookup terms (natural binary)), optionValue (tableTerms[binary]?)]) with
      | none => rfl
      | some bound =>
          obtain ⟨id, declaration, _, found, shape⟩ := termPattern_match_fields _ _ matched
          have same : entry = declaration := by simpa only [declared, Option.some.injEq] using found
          exact False.elim (malformed (same ▸ shape))
  | @pop identifier sort ret value formalArguments resolved declared refused =>
      let declaration : Atom := .expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]
      let selected := ("value", value) :: ("ret", ret) :: ("args", .expression formalArguments) ::
        ("sort", sort) :: ("id", identifier) :: entered
      rw [term_case_shape]
      apply case_returns program entered selected state state state (.expression [.var "found", .var "entry"])
        (.expression [optionValue (some identifier), optionValue (some declaration)]) termFound _ _
        termCases (read_cases_encoded termCases)
      · simpa [entered, bindings, termEnvironment, resolved, declared, declaration, applySubst, Subst.lookup] using
          tuple_variables_return program entered state ["found", "entry"]
      · simp [term_cases_shape, declaration, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected, entered, bindings,
          termEnvironment, resolved, declared, optionValue, listValue]
      · rw [term_found_shape]
        let denied := ("bad", .symbol "None") :: selected
        apply case_returns program selected denied state state state _ (.symbol "None") (.symbol "None") _ _
          termPopCases (read_cases_encoded termPopCases)
        · exact computed_pop_returns selected state formalArguments stack none rfl rfl refused
        · simp [term_pop_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            matchAtom, denied, selected, entered, bindings, termEnvironment, Subst.lookup]
        · exact symbol_returns program denied state "None"

/-- Original constructor refusals retain the exact effect state and return one
explicit None answer; they do not silently become an empty answer bag. -/
theorem Refusal.returns {terms : List MMUResolution.Binding} {tableTerms stack : List Atom} {binary : Nat}
    (refusal : Refusal terms tableTerms binary stack) (bindings : Subst) (state : State) (published : Atom)
    (sorts theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images tableSorts tableTheorems : Atom) (next arity count : Nat) (heap dummies hypotheses saved : List Atom) (save : Bool)
    (resolverName tablesName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var stateName) = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var resolverName, .var tablesName, .var stateName, .var binaryName, .var saveName]) state (.symbol "None") := by
  apply authored_variable_call_returns program
    bindings (termEnvironment (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save)
    state state "mm0:mmb:proof-term" [resolverName, tablesName, stateName, binaryName, saveName] termEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (refusal.body_returns state published sorts theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
      next arity count heap dummies hypotheses saved save) (by decide)
  simpa [resolverCaptured, tablesCaptured, stateCaptured, binaryCaptured, saveCaptured] using
    term_clause _ tableSorts tableTheorems tableTerms next arity count stack heap dummies hypotheses saved binary save

private def stepEquation := sourceEquation "mm0:mmb:proof-step"
private def stepCondition : Atom :=
  .expression [.symbol "or", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBAssertion"],
    .expression [.symbol "and", .expression [.symbol "==", .var "mode", .symbol "MM0:MMBDefinition"],
      .expression [.symbol "is-member", .var "opcode", .expression [natural 16, natural 17, natural 18, natural 19, natural 31]]]]
private def stepCases : SpaceSemantics.Cases :=
  match stepEquation.body with
  | .expression [_, _, .expression [_, _, .expression rows], _] => (readCases rows).getD []
  | _ => []
private def stepEnvironment (resolver tables formal before : Atom) (opcode data start after : Nat) : Subst :=
  [("after", natural after), ("start", natural start), ("data", natural data), ("opcode", natural opcode),
    ("state", before), ("mode", .symbol "MM0:MMBAssertion"), ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem step_unique : program.equations.filter (·.head == "mm0:mmb:proof-step") = [stepEquation] := by decide +kernel
private theorem step_formals : stepEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"]] := by decide
private theorem step_shape : stepEquation.body =
    .expression [.symbol "if", stepCondition,
      .expression [.symbol "case", .var "opcode", .expression (stepCases.map fun row => .expression [row.1, row.2])], .symbol "None"] := by decide
private theorem stepCases_shape : stepCases =
  [(natural 16, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean false]),
   (natural 17, .expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean true]),
   (natural 18, .expression [.symbol "mm0:mmb:proof-reference", .var "state", .var "data"]),
   (natural 19, .expression [.symbol "mm0:mmb:proof-dummy", .var "resolver", .var "state", .var "data"]),
   (natural 20, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean false]),
   (natural 21, .expression [.symbol "mm0:mmb:proof-theorem", .var "resolver", .var "tables", .var "formal", .var "state", .var "data", boolean true]),
   (natural 22, .expression [.symbol "mm0:mmb:proof-hypothesis", .var "state"]),
   (natural 23, .expression [.symbol "mm0:mmb:proof-conversion", .var "state"]),
   (natural 24, .expression [.symbol "mm0:mmb:proof-reflexivity", .var "state"]),
   (natural 25, .expression [.symbol "mm0:mmb:proof-symmetry", .var "state"]),
   (natural 26, .expression [.symbol "mm0:mmb:proof-congruence", .var "resolver", .var "state"]),
   (natural 27, .expression [.symbol "mm0:mmb:proof-unfold", .var "resolver", .var "tables", .var "formal", .var "state"]),
   (natural 28, .expression [.symbol "mm0:mmb:proof-cut", .var "state"]),
   (natural 30, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean true]),
   (natural 31, .expression [.symbol "mm0:mmb:proof-save", .var "state", boolean false]), (.var "bad", .symbol "None")] := by decide
private theorem step_clause (resolver tables formal before : Atom) (opcode data start after : Nat) :
    clauses program "mm0:mmb:proof-step" [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, MMBExecution.commandValue opcode data start after] =
      [.evaluate (stepEnvironment resolver tables formal before opcode data start after) stepEquation.body] := by
  rw [clauses_use_only_the_named_equations, step_unique]
  simp [step_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, stepEnvironment, MMBExecution.commandValue]

private theorem step_condition_returns (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (supported : opcode = 16 ∨ opcode = 17 ∨ opcode = 19) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepCondition state (boolean true) := by
  apply completed_run_has_path program 100 _ state [boolean true] [] []
  rcases supported with rfl | rfl | rfl <;> rfl

private theorem step_body_from_call (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (call result : Atom)
    (supported : opcode = 16 ∨ opcode = 17 ∨ opcode = 19)
    (selected : SpaceSemantics.selectCase (stepEnvironment resolver tables formal before opcode data start after) (natural opcode) stepCases =
      some (stepEnvironment resolver tables formal before opcode data start after, call))
    (computed : PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state call state result) :
    PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepEquation.body state result := by
  rw [step_shape]
  apply if_returns program _ state state state _ (boolean true) _ _ _
    (step_condition_returns state resolver tables formal before opcode data start after supported)
  simp only [boolean, beq_self_eq_true, ↓reduceIte]
  exact case_returns program _ _ state state state (.var "opcode") (natural opcode) call _ _ stepCases
    (read_cases_encoded stepCases) (variable_returns program _ state "opcode") selected computed

private theorem step_raw_from_body (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Atom)
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (body : PureReturns program (stepEnvironment resolver tables formal before opcode data start after) state stepEquation.body state result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName,
      .var formalName, .var modeName, .var stateName, .var codeName]) state result := by
  apply authored_variable_call_returns program bindings (stepEnvironment resolver tables formal before opcode data start after)
    state state "mm0:mmb:proof-step" [resolverName, tablesName, formalName, modeName, stateName, codeName] stepEquation.body result
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ body (by decide)
  simpa [resolverCaptured, tablesCaptured, formalCaptured, modeCaptured, stateCaptured, codeCaptured] using
    step_clause resolver tables formal before opcode data start after



private theorem Refusal.literal_returns {terms : List MMUResolution.Binding} {tableTerms stack : List Atom} {binary : Nat}
    (refusal : Refusal terms tableTerms binary stack) (bindings : Subst) (state : State) (published : Atom)
    (sorts theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images tableSorts tableTheorems : Atom) (next arity count : Nat) (heap dummies hypotheses saved : List Atom) (save : Bool)
    (resolverCaptured : applySubst bindings (.var "resolver") =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var "tables") =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var "state") = stateValue next arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var "data") = natural binary) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var "resolver", .var "tables", .var "state", .var "data", boolean save]) state (.symbol "None") := by
  let prior : Subst := [("r", MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images),
    ("t", .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems]),
    ("s", stateValue next arity count stack heap dummies hypotheses saved), ("b", natural binary), ("v", boolean save)]
  have original := refusal.returns prior state published sorts theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
    next arity count heap dummies hypotheses saved save "r" "t" "s" "b" "v" rfl rfl rfl rfl rfl
  apply captured_call_returns program prior bindings state state "mm0:mmb:proof-term"
    [.var "r", .var "t", .var "s", .var "b", .var "v"]
    [.var "resolver", .var "tables", .var "state", .var "data", boolean save] _
    (by decide +kernel) (by decide) _ _ _ original
  · intro offset argument selected
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr rfl
  · intro offset argument selected
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals exact Or.inr (by cases save <;> rfl)
  · simp only [List.map_cons, List.map_nil, resolverCaptured, tablesCaptured, stateCaptured, binaryCaptured]
    cases save <;> rfl

/-- This extends the original allocated-command evidence by its exhaustive
constructor refusal cases. Allocation histories remain logical evidence;
the executing source is unchanged. -/
inductive Command (terms : List MMUResolution.Binding) (resolver tables : Atom) :
    List Atom → Atom → Nat → Nat → Option (List Atom × Atom) → Prop where
  | admitted {history : List Atom} {before : Atom} {opcode data : Nat} {result : Option (List Atom × Atom)}
      (trace : MMBAllocationRunExecution.Command terms resolver tables history before opcode data result) :
      Command terms resolver tables history before opcode data result
  | refused {published images tableSorts tableTheorems : Atom} {sorts theorems : List MMUResolution.Binding}
      {nextSort nextTerm nextTheorem binary arity count : Nat} {tableTerms history stack heap dummies hypotheses saved : List Atom}
      (save : Bool)
      (resolverShape : resolver = MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (tablesShape : tables = .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      (refusal : Refusal terms tableTerms binary stack) :
      Command terms resolver tables history (stateValue history.length arity count stack heap dummies hypotheses saved)
        (if save then 17 else 16) binary none

/-- Successful constructors retain the complete original allocation/current-map
invariant; refusal supplies no successor state and leaves no new authority. -/
theorem Command.authority {terms : List MMUResolution.Binding} {resolver tables : Atom}
    {history : List Atom} {before : Atom} {opcode data : Nat} {result : Option (List Atom × Atom)}
    (trace : Command terms resolver tables history before opcode data result)
    (built : ConstructedHistory history) (resolved : MMBAllocationResolution.ResolvedHistory terms history)
    (authorized : StateAuthority history before) :
    ∀ afterHistory after, result = some (afterHistory, after) →
      ConstructedHistory afterHistory ∧ MMBAllocationResolution.ResolvedHistory terms afterHistory ∧ StateAuthority afterHistory after := by
  cases trace with
  | admitted trace => exact trace.authority built resolved authorized
  | refused => intro afterHistory after impossible; cases impossible

/-- Every earned constructor branch executes through the unchanged binary
opcode dispatcher, with complete command interval metadata retained. -/
theorem Command.step_returns {terms : List MMUResolution.Binding} {history : List Atom}
    (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option (List Atom × Atom))
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (trace : Command terms resolver tables history before opcode data result) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName,
      .var formalName, .var modeName, .var stateName, .var codeName]) state (optionValue (result.map Prod.snd)) := by
  cases trace with
  | admitted trace =>
      exact trace.step_returns bindings state resolver tables formal before opcode data start after result
        resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured
  | @refused published images tableSorts tableTheorems sorts theorems nextSort nextTerm nextTheorem binary arity count tableTerms history stack heap dummies hypotheses saved save resolverShape tablesShape refusal =>
      apply step_raw_from_body bindings state resolver tables formal _ _ _ start after _
        resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured
      cases save with
      | false =>
          apply step_body_from_call state resolver tables formal _ 16 data start after
            (.expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean false]) _ (Or.inl rfl)
          · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
          · apply refusal.literal_returns _ state published sorts theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
              history.length arity count heap dummies hypotheses saved false _ _ rfl rfl
            · change resolver = _; exact resolverShape
            · change tables = _; exact tablesShape
      | true =>
          apply step_body_from_call state resolver tables formal _ 17 data start after
            (.expression [.symbol "mm0:mmb:proof-term", .var "resolver", .var "tables", .var "state", .var "data", boolean true]) _ (Or.inr (Or.inl rfl))
          · simp [stepCases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
          · apply refusal.literal_returns _ state published sorts theorems nextSort nextTerm nextTheorem images tableSorts tableTheorems
              history.length arity count heap dummies hypotheses saved true _ _ rfl rfl
            · change resolver = _; exact resolverShape
            · change tables = _; exact tablesShape

/-- Exhaustive constructor classification under original map/row admission
and chronological stack authority. The success case earns its pop and full
preterm projection; the other cases earn exact original refusal. -/
theorem term_total (published images tableSorts tableTheorems : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem binary arity count : Nat)
    (tableTerms history stack heap dummies hypotheses saved : List Atom) (save : Bool)
    (numeric : MMUResolution.NumericalMap terms) (rows : ArgumentListRows tableTerms)
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses) :
    ∃ result, Command terms
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (.expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      history (stateValue history.length arity count stack heap dummies hypotheses saved)
      (if save then 17 else 16) binary result := by
  classical
  cases lookup : MMUResolution.lookup terms (natural binary) with
  | none => exact ⟨none, .refused save rfl rfl (.missingName lookup)⟩
  | some identifier =>
      obtain ⟨logical, rfl⟩ := MMUResolution.numerical_lookup terms (natural binary) identifier numeric lookup
      cases declared : tableTerms[binary]? with
      | none => exact ⟨none, .refused save rfl rfl (.missingDeclaration declared)⟩
      | some declaration =>
          by_cases shape : DeclarationShape declaration
          · obtain ⟨sort, formals, ret, value, rfl⟩ := rows declaration (List.mem_of_getElem? declared) shape
            obtain ⟨result, popped⟩ := MMBTheoremCommandExecution.Pops.total .expressions formals.length stack
            cases result with
            | none => exact ⟨none, .refused save rfl rfl (.pop lookup declared popped)⟩
            | some pair =>
                obtain ⟨arguments, rest⟩ := pair
                obtain ⟨values, projected⟩ := MMBAllocationRunExecution.popped_expression_claims built coherent.2.1 popped
                exact ⟨_, .admitted (.term save rfl rfl lookup declared popped projected)⟩
          · exact ⟨none, .refused save rfl rfl (.malformedDeclaration declared shape)⟩

/-- Dummy allocation uses the current original sort map; every missing sort
refuses and every present metadata atom is retained without reinterpretation. -/
theorem dummy_total (published images tableSorts tableTheorems : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem binary arity count : Nat)
    (tableTerms history stack heap dummies hypotheses saved : List Atom) :
    ∃ result, Command terms
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (.expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      history (stateValue history.length arity count stack heap dummies hypotheses saved) 19 binary result := by
  cases lookup : MMUResolution.lookup sorts (natural binary) with
  | none => exact ⟨none, .admitted (.missingDummy rfl lookup)⟩
  | some sort => exact ⟨_, .admitted (.dummy rfl lookup)⟩

/-- Every well-shaped, admitted original constructor command has an exact
completed source answer and retains chronological authority whenever it
succeeds. This theorem does not assume a completed target observation. -/
theorem constructor_total_returns (state : State) (published images tableSorts tableTheorems formal : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem opcode binary start after arity count : Nat)
    (tableTerms history stack heap dummies hypotheses saved : List Atom)
    (supported : opcode = 16 ∨ opcode = 17 ∨ opcode = 19)
    (numeric : MMUResolution.NumericalMap terms) (rows : ArgumentListRows tableTerms)
    (built : ConstructedHistory history) (resolved : MMBAllocationResolution.ResolvedHistory terms history)
    (coherent : StateCoherent history stack heap hypotheses) :
    ∃ result, Command terms
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (.expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      history (stateValue history.length arity count stack heap dummies hypotheses saved) opcode binary result ∧
      PureReturns program [] state (.expression [.symbol "mm0:mmb:proof-step",
        MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images,
        .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems], formal, .symbol "MM0:MMBAssertion",
        stateValue history.length arity count stack heap dummies hypotheses saved, MMBExecution.commandValue opcode binary start after])
        state (optionValue (result.map Prod.snd)) ∧
      (∀ afterHistory afterState, result = some (afterHistory, afterState) →
        ConstructedHistory afterHistory ∧ MMBAllocationResolution.ResolvedHistory terms afterHistory ∧ StateAuthority afterHistory afterState) := by
  obtain ⟨result, trace⟩ : ∃ result, Command terms
      (MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
      (.expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
      history (stateValue history.length arity count stack heap dummies hypotheses saved) opcode binary result := by
    rcases supported with rfl | rfl | rfl
    · exact term_total published images tableSorts tableTheorems sorts terms theorems nextSort nextTerm nextTheorem binary arity count
        tableTerms history stack heap dummies hypotheses saved false numeric rows built coherent
    · exact term_total published images tableSorts tableTheorems sorts terms theorems nextSort nextTerm nextTheorem binary arity count
        tableTerms history stack heap dummies hypotheses saved true numeric rows built coherent
    · exact dummy_total published images tableSorts tableTheorems sorts terms theorems nextSort nextTerm nextTheorem binary arity count
        tableTerms history stack heap dummies hypotheses saved
  let resolver := MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images
  let tables : Atom := .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems]
  let before := stateValue history.length arity count stack heap dummies hypotheses saved
  let code := MMBExecution.commandValue opcode binary start after
  let bindings : Subst := [("r", resolver), ("t", tables), ("f", formal), ("m", .symbol "MM0:MMBAssertion"), ("s", before), ("c", code)]
  have executed := trace.step_returns bindings state resolver tables formal before opcode binary start after result
    "r" "t" "f" "m" "s" "c" rfl rfl rfl rfl rfl rfl
  refine ⟨result, trace, ?_, trace.authority built resolved (StateAuthority.mk arity count coherent)⟩
  apply raw_call_returns program [] state state "mm0:mmb:proof-step" _ _ (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · have finished := captured_function_arguments_returns program bindings [] state state "mm0:mmb:proof-step"
      [.var "r", .var "t", .var "f", .var "m", .var "s", .var "c"] 6 _ (by decide +kernel) (by decide)
      (by intro offset argument selected; exact Or.inl (by
        have bound := (getElem?_eq_some_iff.mp selected).choose
        have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by simp only [List.length_cons, List.length_nil] at bound; omega
        rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)) executed
    simpa [bindings, resolver, tables, before, code, applySubst, applySubst.applySubstList, applySubst_nil, Subst.lookup] using finished


/-- A constructor cannot consume more physical entries than are present.
This earns underflow from the actual ordered pop relation. -/
theorem pops_refused_of_short (kind : MMBTheoremCommandExecution.StackKind) (count : Nat) (stack : List Atom)
    (short : stack.length < count) : MMBTheoremCommandExecution.Pops kind count stack none := by
  obtain ⟨result, trace⟩ := MMBTheoremCommandExecution.Pops.total kind count stack
  cases result with
  | none => exact trace
  | some pair =>
      obtain ⟨items, remaining⟩ := pair
      obtain ⟨counted, ordered⟩ := trace.ordered
      have lengths := congrArg List.length ordered
      simp only [List.length_append, List.length_reverse] at lengths
      omega

/-- Out-of-range physical declaration positions are original refusals even
when the resolver contains that binary name. -/
theorem Refusal.future_declaration (terms : List MMUResolution.Binding) (tableTerms stack : List Atom) (binary : Nat)
    (future : tableTerms.length ≤ binary) : Refusal terms tableTerms binary stack :=
  .missingDeclaration (List.getElem?_eq_none future)

/-- Stack underflow is earned independently of logical expression values. -/
theorem Refusal.underflow {terms : List MMUResolution.Binding} {tableTerms stack formalArguments : List Atom}
    {binary : Nat} {identifier sort ret value : Atom}
    (resolved : MMUResolution.lookup terms (natural binary) = some identifier)
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (short : stack.length < formalArguments.length) : Refusal terms tableTerms binary stack :=
  .pop resolved declared (pops_refused_of_short .expressions formalArguments.length stack short)

/-- A proof or conversion entry cannot be consumed as a constructor argument.
The source rejects that physical stack position before later entries. -/
theorem Refusal.wrong_kind {terms : List MMUResolution.Binding} {tableTerms rest formalArguments : List Atom}
    {binary : Nat} {identifier sort ret value first : Atom}
    (resolved : MMUResolution.lookup terms (natural binary) = some identifier)
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (required : 0 < formalArguments.length)
    (rejected : MMBTheoremCommandExecution.StackKind.accepts .expressions first = false) :
    Refusal terms tableTerms binary (first :: rest) := by
  obtain ⟨count, length⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : formalArguments.length ≠ 0)
  exact .pop resolved declared (by rw [length]; exact .wrong count first rest rejected)

/-- A completed original dispatcher observation is uniquely the qualified
optional successor state. State cells, input and output remain unchanged. -/
theorem Command.step_completed_exact {terms : List MMUResolution.Binding} {history : List Atom}
    (bindings : Subst) (state : State) (resolver tables formal before : Atom)
    (opcode data start after : Nat) (result : Option (List Atom × Atom))
    (resolverName tablesName formalName modeName stateName codeName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) = resolver)
    (tablesCaptured : applySubst bindings (.var tablesName) = tables)
    (formalCaptured : applySubst bindings (.var formalName) = formal)
    (modeCaptured : applySubst bindings (.var modeName) = .symbol "MM0:MMBAssertion")
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (codeCaptured : applySubst bindings (.var codeName) = MMBExecution.commandValue opcode data start after)
    (trace : Command terms resolver tables history before opcode data result)
    (fuel : Nat) (finishedState : State) (answers input output : List Atom)
    (completed : Eval.run program fuel {state := state, control := .evaluate bindings (.expression [.symbol "mm0:mmb:proof-step", .var resolverName, .var tablesName,
        .var formalName, .var modeName, .var stateName, .var codeName])} = .complete finishedState answers input output) :
    finishedState = state ∧ answers = [optionValue (result.map Prod.snd)] ∧ input = [] ∧ output = [] := by
  exact (pure_returns_completed_iff program bindings state state _ _
    (trace.step_returns bindings state resolver tables formal before opcode data start after result
      resolverName tablesName formalName modeName stateName codeName resolverCaptured tablesCaptured formalCaptured modeCaptured stateCaptured codeCaptured)
    finishedState answers input output).mp ⟨fuel, completed⟩

private def runEquation := sourceEquation "mm0:mmb:proof-run"
private def runCases := casesOf runEquation.body
private def runCons := (runCases[1]'(by decide)).2
private def runConsCases := casesOf runCons
private def runTail := (runConsCases[0]'(by decide)).2
private def runEnvironment (resolver tables formal before : Atom) (commands : List Atom) : Subst :=
  [("codes", .expression commands), ("state", before), ("mode", .symbol "MM0:MMBAssertion"),
    ("formal", formal), ("tables", tables), ("resolver", resolver)]
private theorem run_unique : program.equations.filter (·.head == "mm0:mmb:proof-run") = [runEquation] := by decide +kernel
private theorem run_formals : runEquation.arguments =
    [.var "resolver", .var "tables", .var "formal", .var "mode", .var "state",
      .expression [.symbol "MM0:L", .var "codes"]] := by decide
private theorem run_shape : runEquation.body =
    .expression [.symbol "case", .var "codes",
      .expression (runCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cases_shape : runCases =
    [(.expression [], .expression [.symbol "Some", .var "state"]),
     (.expression [.symbol "cons", .var "first", .var "rest"], runCons),
     (.var "bad", .symbol "None")] := by decide
private theorem run_cons_shape : runCons =
    .expression [.symbol "case", .expression [.symbol "mm0:mmb:proof-step", .var "resolver", .var "tables", .var "formal",
      .var "mode", .var "state", .var "first"],
      .expression (runConsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem run_cons_cases_shape : runConsCases =
    [(.expression [.symbol "Some", .var "after"], runTail), (.var "bad", .symbol "None")] := by decide
private theorem run_tail_shape : runTail =
    .expression [.symbol "mm0:mmb:proof-run", .var "resolver", .var "tables", .var "formal", .var "mode",
      .var "after", .expression [.symbol "MM0:L", .var "rest"]] := by decide
private theorem run_clause (resolver tables formal before : Atom) (commands : List Atom) :
    clauses program "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] =
      [.evaluate (runEnvironment resolver tables formal before commands) runEquation.body] := by
  rw [clauses_use_only_the_named_equations, run_unique]
  simp [run_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, runEnvironment, listValue]

private theorem raw_run_from_body (bindings : Subst) (state : State)
    (resolver tables formal before : Atom) (commands : List Atom) (result : Option Atom)
    (arguments : List Atom)
    (captured : arguments.map (applySubst bindings) =
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands])
    (body : PureReturns program (runEnvironment resolver tables formal before commands)
      state runEquation.body state (optionValue result)) :
    PureReturns program bindings state (.expression (.symbol "mm0:mmb:proof-run" :: arguments))
      state (optionValue result) := by
  have length : arguments.length = 6 := by
    have sizes := congrArg List.length captured
    simpa using sizes
  apply raw_call_returns program bindings state state "mm0:mmb:proof-run" arguments _
    (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    rw [length] at bounded
    have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 ∨ offset = 5 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rw [captured, length]
    exact authored_function_arguments_return program bindings
      (runEnvironment resolver tables formal before commands) state state "mm0:mmb:proof-run"
      [resolver, tables, formal, .symbol "MM0:MMBAssertion", before, listValue commands] 6
      runEquation.body _ (by decide) (by decide) (run_clause resolver tables formal before commands) body


/-- An original constructor refusal stops the recursive proof runner before
any suffix operation, even when that suffix is malformed or effectful. -/
theorem refused_run_returns {terms : List MMUResolution.Binding} {history : List Atom}
    (state : State) (resolver tables formal before : Atom) (opcode data start after : Nat)
    (rest : List Atom) (refused : Command terms resolver tables history before opcode data none) :
    PureReturns program [] state
      (.expression [.symbol "mm0:mmb:proof-run", resolver, tables, formal, .symbol "MM0:MMBAssertion", before,
        listValue (MMBExecution.commandValue opcode data start after :: rest)]) state (.symbol "None") := by
  apply raw_run_from_body [] state resolver tables formal before
    (MMBExecution.commandValue opcode data start after :: rest) none _
    (by simp only [List.map_cons, List.map_nil, applySubst_nil])
  let command := MMBExecution.commandValue opcode data start after
  let bindings := runEnvironment resolver tables formal before (command :: rest)
  let bound := ("rest", .expression rest) :: ("first", command) :: bindings
  let stopped := ("bad", .symbol "None") :: bound
  rw [run_shape]
  apply case_returns program bindings bound state state state (.var "codes")
    (.expression (command :: rest)) runCons _ _ runCases (read_cases_encoded runCases)
  · exact variable_returns program bindings state "codes"
  · simp [run_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, bound, bindings, runEnvironment]
  · rw [run_cons_shape]
    apply case_returns program bound stopped state state state _ (.symbol "None") (.symbol "None")
      _ _ runConsCases (read_cases_encoded runConsCases)
    · apply Command.step_returns bound state resolver tables formal before opcode data start after none
        "resolver" "tables" "formal" "mode" "state" "first" _ _ _ _ _ rfl refused
      all_goals simp [bound, bindings, runEnvironment, applySubst, Subst.lookup]
    · simp [run_cons_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        matchAtom, Subst.lookup, stopped, bound, bindings, runEnvironment]
    · exact symbol_returns program stopped state "None"

/-- The exact refusal observation has sufficient fuel and cannot become an
empty answer bag, a successful state or an I/O-producing suffix execution. -/
theorem refused_run_completed_iff {terms : List MMUResolution.Binding} {history : List Atom}
    (state : State) (resolver tables formal before : Atom) (opcode data start after : Nat)
    (rest : List Atom) (refused : Command terms resolver tables history before opcode data none)
    (observedState : State) (answers input output : List Atom) :
    (∃ fuel, Eval.run program fuel
      {state, control := .evaluate [] (.expression [.symbol "mm0:mmb:proof-run", resolver, tables, formal,
        .symbol "MM0:MMBAssertion", before, listValue (MMBExecution.commandValue opcode data start after :: rest)])} =
      .complete observedState answers input output) ↔
    observedState = state ∧ answers = [.symbol "None"] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (refused_run_returns state resolver tables formal before opcode data start after rest refused)
    observedState answers input output

end Mettapedia.Languages.MM0.MeTTa.MMBConstructorExecution
