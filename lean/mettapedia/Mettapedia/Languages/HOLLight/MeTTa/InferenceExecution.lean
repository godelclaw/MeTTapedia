import Mettapedia.Languages.HOLLight.MeTTa.Transitivity
import Mettapedia.Languages.HOLLight.MeTTa.ProofLookup
import Mettapedia.Languages.HOLLight.MeTTa.TermReading
import Mettapedia.Languages.HOLLight.MeTTa.Application
import Mettapedia.Languages.HOLLight.MeTTa.EqualityModusPonens
import Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata

/-!
# Authored inference dispatch from the complete HOL state

Reflexivity and assumption execute the registered source reader. Assumption
additionally enforces its Boolean-conclusion gate. Transitivity executes the
actual inference dispatcher and its two ordered
proof-cache lookups. The operation preserves declaration tables, commitments,
the cache and receipts while constructing the source result. Cache-history
validity and admission of that result are distinct obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open SignatureFormation
open Representation (registeredOperatorAtom termAtom)
open TypeSubstitution (typeAtom)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def transBody : Atom := .expression [.symbol "hol-light:trans",
  .expression [.symbol "hol-light:known", .var "state", .var "first"],
  .expression [.symbol "hol-light:known", .var "state", .var "second"]]

private def environment (source request : Atom) : Subst := [("request", request), ("state", source)]

private theorem shape : equation.body = .expression [.symbol "case", .var "request",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem clause (source request : Atom) : clauses program "hol-light:infer" [source, request] =
    [.evaluate (environment source request) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:infer") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def readEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:read"))[0]'(by decide)

private def readEnvironment (operators constants axioms receipts term : Atom)
    (cache : List (Atom × Atom)) : Subst :=
  [("term", term), ("receipts", receipts), ("cache", Lookup.table cache),
    ("axioms", axioms), ("constants", constants), ("operators", operators)]

private theorem read_shape : readEquation.body = .expression [.symbol "hol-light:read-term",
    .var "operators", .var "constants", .symbol "HOL:Nil", .var "term"] := by decide

private theorem read_clause (operators constants axioms receipts term : Atom)
    (cache : List (Atom × Atom)) :
    clauses program "hol-light:read" [ProofLookup.sourceState operators constants axioms receipts cache, term] =
      [.evaluate (readEnvironment operators constants axioms receipts term cache) readEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:read") = [readEquation] := by rfl
  rw [unique]
  have formals : readEquation.arguments = [.expression [.symbol "HOL:State", .var "operators", .var "constants",
    .var "axioms", .var "cache", .var "receipts"], .var "term"] := by decide
  simp [formals, ProofLookup.sourceState, readEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Constructed source arguments use the same state reader as captured
arguments. Their actual evaluations are retained in the execution path. -/
theorem authored_state_read_computed_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateExpression termExpression : Atom)
    (stateReturned : PureReturns program bindings state stateExpression state (ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache))
    (termReturned : PureReturns program bindings state termExpression state (TermReading.sourceAtom source)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read", stateExpression, termExpression]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] (source.toDB [])]) := by
  let before := readEnvironment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts (TermReading.sourceAtom source) cache
  apply authored_binary_call_returns program bindings before state state state state "hol-light:read"
    stateExpression termExpression _ _ readEquation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) stateReturned termReturned
    (read_clause _ _ _ _ _ cache) _ (by decide)
  rw [read_shape]
  apply TermReading.authored_read_computed_return world table origins constants source resolved []
    (by simp) annotations type typed before state (.var "operators") (.var "constants")
    (.symbol "HOL:Nil") (.var "term")
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using variable_returns program before state "operators"
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using variable_returns program before state "constants"
  · exact symbol_returns program before state "HOL:Nil"
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using variable_returns program before state "term"

theorem authored_state_read_computed_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateExpression termExpression : Atom)
    (stateReturned : BoundCalls.CorePath.PureReturns program bindings state stateExpression state (ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache))
    (termReturned : BoundCalls.CorePath.PureReturns program bindings state termExpression state (TermReading.sourceAtom source)) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read", stateExpression, termExpression]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] (source.toDB [])]) := by
  let before := readEnvironment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts (TermReading.sourceAtom source) cache
  apply BoundCalls.CorePath.authored_binary_call_returns program bindings before state state state state "hol-light:read"
    stateExpression termExpression _ _ readEquation.body _
    (by decide) (by decide) (by decide) (by decide) (by decide) stateReturned termReturned
    (read_clause _ _ _ _ _ cache) _ (by decide)
  rw [read_shape]
  apply TermReading.authored_read_computed_certificate world table origins constants source resolved []
    (by simp) annotations type typed before state (.var "operators") (.var "constants")
    (.symbol "HOL:Nil") (.var "term")
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "operators"
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "constants"
  · exact BoundCalls.CorePath.symbol_returns program before state "HOL:Nil"
  · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "term"


/-- The source state supplies the registered signature to its reader. The
cache, commitments and receipts remain intact and do not authorize the term. -/
theorem authored_state_read_certificate (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey termKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (termCaptured : applySubst bindings (.var termKey) = TermReading.sourceAtom source) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:read", .var stateKey, .var termKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] (source.toDB [])]) := by
  let before := readEnvironment (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts (TermReading.sourceAtom source) cache
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings before state state "hol-light:read" [stateKey, termKey]
    readEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, termCaptured] using
      read_clause (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        axioms receipts (TermReading.sourceAtom source) cache
  · rw [read_shape]
    apply TermReading.authored_read_computed_certificate world table origins constants source resolved []
      (by simp) annotations type typed before state (.var "operators") (.var "constants")
      (.symbol "HOL:Nil") (.var "term")
    · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "operators"
    · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "constants"
    · exact BoundCalls.CorePath.symbol_returns program before state "HOL:Nil"
    · simpa [before, readEnvironment, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program before state "term"


theorem authored_state_read_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey termKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (termCaptured : applySubst bindings (.var termKey) = TermReading.sourceAtom source) :
    PureReturns program bindings state (.expression [.symbol "hol-light:read", .var stateKey, .var termKey]) state
      (.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] (source.toDB [])]) :=
  (authored_state_read_certificate world table origins constants source resolved annotations type typed
    bindings state axioms receipts cache stateKey termKey stateCaptured termCaptured).original

private def reflSelected : Atom := .expression [.symbol "hol-light:theorem-eq", .symbol "HOL:Nil",
  .var "value", .var "value", .symbol "HOL:Nil", .symbol "REFL"]
private def readCases (selected : Atom) : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "value"], selected), (.var "malformed", .symbol "None")]
private def sourceBody (selected : Atom) : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:read", .var "state", .var "term"],
  .expression ((readCases selected).map fun row => .expression [row.1, row.2])]

private def assumeResult : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:Thm", .expression [.symbol "HOL:Cons", .var "value", .symbol "HOL:Nil"],
    .var "value", .symbol "HOL:Nil", .symbol "ASSUME"]]
private def assumeSelected : Atom := .expression [.symbol "if", .expression [.symbol "==",
  .expression [.symbol "hol-light:term-type", .var "value"],
  .expression [.symbol "Some", .expression [.symbol "hol-light:bool"]]], assumeResult, .symbol "None"]

private theorem refl_selected (source term : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "REFL", term]))
      (.expression [.symbol "REFL", term]) cases =
      some (("term", term) :: environment source (.expression [.symbol "REFL", term]), sourceBody reflSelected) := by
  have firstCase : cases = (.expression [.symbol "REFL", .var "term"], sourceBody reflSelected) :: cases.drop 1 := by decide
  rw [firstCase]
  simp [environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem assume_selected (source term : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "ASSUME", term]))
      (.expression [.symbol "ASSUME", term]) cases =
      some (("term", term) :: environment source (.expression [.symbol "ASSUME", term]), sourceBody assumeSelected) := by
  have initialCases : cases =
      (cases[0]'(by decide)) :: (cases[1]'(by decide)) :: (cases[2]'(by decide)) ::
      (cases[3]'(by decide)) :: (cases[4]'(by decide)) ::
      (.expression [.symbol "ASSUME", .var "term"], sourceBody assumeSelected) :: cases.drop 6 := by decide
  have first : (cases[0]'(by decide)).1 = .expression [.symbol "REFL", .var "term"] := by decide
  have second : (cases[1]'(by decide)).1 = .expression [.symbol "TRANS", .var "first", .var "second"] := by decide
  have third : (cases[2]'(by decide)).1 = .expression [.symbol "MK_COMB", .var "first", .var "second"] := by decide
  have fourth : (cases[3]'(by decide)).1 = .expression [.symbol "ABS", .var "variable", .var "premise"] := by decide
  have fifth : (cases[4]'(by decide)).1 = .expression [.symbol "BETA", .var "term"] := by decide
  rw [initialCases]
  simp only [SpaceSemantics.selectCase, first, second, third, fourth, fifth]
  simp [environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem source_body_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (kind : String) (selected answer : Atom)
    (selectedReturned : PureReturns program
      (("value", termAtom registeredOperatorAtom constants [] (source.toDB [])) ::
        ("term", TermReading.sourceAtom source) :: environment
          (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
            (DeclarationTable.tableAtom table constants) axioms receipts cache)
          (.expression [.symbol kind, TermReading.sourceAtom source])) state selected state answer) :
    PureReturns program
      (("term", TermReading.sourceAtom source) :: environment
        (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
          (DeclarationTable.tableAtom table constants) axioms receipts cache)
        (.expression [.symbol kind, TermReading.sourceAtom source])) state (sourceBody selected) state answer := by
  let sourceState := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let before : Subst := ("term", TermReading.sourceAtom source) ::
    environment sourceState (.expression [.symbol kind, TermReading.sourceAtom source])
  let value := termAtom registeredOperatorAtom constants [] (source.toDB [])
  unfold sourceBody
  apply case_returns program before (("value", value) :: before) state state state _
    (.expression [.symbol "Some", value]) selected _ _ (readCases selected) (read_cases_encoded (readCases selected))
  · exact authored_state_read_return world table origins constants source resolved annotations type typed
      before state axioms receipts cache "state" "term"
      (by simp [before, environment, sourceState, applySubst, Subst.lookup])
      (by simp [before, applySubst, Subst.lookup])
  · simp [readCases, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · exact selectedReturned

private theorem dispatch_source_return (state : State) (source term : Atom) (kind : String)
    (selected answer : Atom)
    (selection : SpaceSemantics.selectCase (environment source (.expression [.symbol kind, term]))
      (.expression [.symbol kind, term]) cases =
      some (("term", term) :: environment source (.expression [.symbol kind, term]), sourceBody selected))
    (returned : PureReturns program (("term", term) :: environment source (.expression [.symbol kind, term]))
      state (sourceBody selected) state answer) :
    PureReturns program (environment source (.expression [.symbol kind, term])) state equation.body state answer := by
  rw [shape]
  apply case_returns program _ _ state state state (.var "request") (.expression [.symbol kind, term])
    (sourceBody selected) _ _ cases (read_cases_encoded cases)
  · exact variable_returns program _ state "request"
  · exact selection
  · exact returned

private theorem infer_captured_return (bindings : Subst) (state : State) (source request answer : Atom)
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (requestCaptured : applySubst bindings (.var requestKey) = request)
    (returned : PureReturns program (environment source request) state equation.body state answer) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state answer := by
  apply authored_variable_call_returns program bindings (environment source request) state state "hol-light:infer"
    [stateKey, requestKey] equation.body _ (by decide) (by decide) (by decide) _ returned (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request

/-- A theorem-shaped record is data, not an inference request. Every such
record is refused by the actual dispatcher, regardless of its alleged parts. -/
theorem authored_forged_request_refused (bindings : Subst) (state : State)
    (source hypotheses conclusion dependencies origin : Atom) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression
      [.symbol "HOL:Thm", hypotheses, conclusion, dependencies, origin]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  let forged := Atom.expression [.symbol "HOL:Thm", hypotheses, conclusion, dependencies, origin]
  let before := environment source forged
  let bound := ("unsupported", forged) :: before
  have patterns : cases = [
      (.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2),
      (.expression [.symbol "TRANS", .var "first", .var "second"], (cases[1]'(by decide)).2),
      (.expression [.symbol "MK_COMB", .var "first", .var "second"], (cases[2]'(by decide)).2),
      (.expression [.symbol "ABS", .var "variable", .var "premise"], (cases[3]'(by decide)).2),
      (.expression [.symbol "BETA", .var "term"], (cases[4]'(by decide)).2),
      (.expression [.symbol "ASSUME", .var "term"], (cases[5]'(by decide)).2),
      (.expression [.symbol "EQ_MP", .var "first", .var "second"], (cases[6]'(by decide)).2),
      (.expression [.symbol "DEDUCT_ANTISYM_RULE", .var "first", .var "second"], (cases[7]'(by decide)).2),
      (.expression [.symbol "INST", .var "entries", .var "premise"], (cases[8]'(by decide)).2),
      (.expression [.symbol "INST_TYPE", .var "entries", .var "premise"], (cases[9]'(by decide)).2),
      (.var "unsupported", .symbol "None")] := by decide
  apply infer_captured_return bindings state source forged _ stateKey requestKey stateCaptured requestCaptured
  rw [shape]
  apply case_returns program before bound state state state (.var "request") forged (.symbol "None") _ _ cases
    (read_cases_encoded cases)
  · exact variable_returns program before state "request"
  · rw [patterns]
    simp [forged, bound, before, environment, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · exact symbol_returns program bound state "None"

/-- Reflexivity reads an arbitrary admitted named source term before invoking
the actual equality constructor. No premise or axiom commitment is inserted. -/
theorem authored_infer_refl_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "REFL", TermReading.sourceAtom source]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (.expression [.symbol "Some", Transitivity.theoremValue constants [] type
        (source.toDB []) (source.toDB []) [] [] (.symbol "REFL")]) := by
  apply infer_captured_return bindings state _ _ _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_source_return state _ _ "REFL" reflSelected _ (refl_selected _ _)
  apply source_body_return world table origins constants source resolved annotations type typed state axioms receipts cache
    "REFL" reflSelected
  let bound : Subst := ("value", termAtom registeredOperatorAtom constants [] (source.toDB [])) ::
    ("term", TermReading.sourceAtom source) :: environment
      (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table constants) axioms receipts cache)
      (.expression [.symbol "REFL", TermReading.sourceAtom source])
  have valueCaptured : applySubst bound (.var "value") =
      termAtom registeredOperatorAtom constants [] (source.toDB []) := by
    simp [bound, applySubst, Subst.lookup]
  unfold reflSelected
  have checked : (source.toDB []).inferType [] = some type :=
    (DBTerm.inferType_toDB [] source).trans typed
  apply Equality.authored_theorem_equality_computed_return constants bound state [] (source.toDB []) (source.toDB [])
    type checked checked equalityIdentity (.symbol "HOL:Nil") (.symbol "HOL:Nil") (.symbol "REFL")
    (.symbol "HOL:Nil") (.var "value") (.var "value") (.symbol "HOL:Nil") (.symbol "REFL")
  · exact symbol_returns program _ state "HOL:Nil"
  · simpa only [valueCaptured] using variable_returns program bound state "value"
  · simpa only [valueCaptured] using variable_returns program bound state "value"
  · exact symbol_returns program _ state "HOL:Nil"
  · exact symbol_returns program _ state "REFL"

private theorem assume_selected_return (world : DefinitionAdapters.TheoryContext)
    (constants : Const → Atom) (value : DBTerm) (type : Ty)
    (typed : value.inferType [] = some type) (formed : TypeFormed world.signature type)
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (bindings : Subst) (state : State)
    (captured : applySubst bindings (.var "value") = termAtom registeredOperatorAtom constants [] value) :
    PureReturns program bindings state assumeSelected state
      (if Ty.same type Ty.bool then .expression [.symbol "Some", .expression [.symbol "HOL:Thm",
        Premises.keys [termAtom registeredOperatorAtom constants [] value],
        termAtom registeredOperatorAtom constants [] value, .symbol "HOL:Nil", .symbol "ASSUME"]]
       else .symbol "None") := by
  have condition := Equality.authored_boolean_test_return world constants bindings state [] value type
    typed formed booleanFormed "value" captured
  unfold assumeSelected
  by_cases isBool : Ty.same type Ty.bool = true
  · simp only [isBool, ↓reduceIte]
    apply if_returns program bindings state state state _ (boolean true) _ _ _
      (by simpa [isBool] using condition)
    unfold assumeResult
    apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide) (by decide)
    apply PureData.constructor_return program bindings state "HOL:Thm" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · simpa [Premises.keys, captured] using
        binary_constructor_returns program bindings state state state "HOL:Cons"
          (.var "value") (.symbol "HOL:Nil") _ _ (by decide) (by decide)
          (variable_returns program bindings state "value") (symbol_returns program bindings state "HOL:Nil")
    · simpa only [captured] using variable_returns program bindings state "value"
    · exact symbol_returns program bindings state "HOL:Nil"
    · exact symbol_returns program bindings state "ASSUME"
  · simp only [isBool]
    apply if_returns program bindings state state state _ (boolean false) _ _ _
      (by simpa [isBool] using condition)
    simpa [boolean] using symbol_returns program bindings state "None"

/-- Assumption accepts exactly the Boolean carrier among resolved, well-typed
source terms. A formed non-Boolean carrier still returns refusal. -/
theorem authored_infer_assume_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : SourceTerm) (resolved : TermReading.SourceResolved world.signature source)
    (annotations : AnnotationsFormed world.signature (source.toDB []))
    (type : Ty) (typed : source.inferType = some type) (formed : TypeFormed world.signature type)
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (if Ty.same type Ty.bool then .expression [.symbol "Some", .expression [.symbol "HOL:Thm",
        Premises.keys [termAtom registeredOperatorAtom constants [] (source.toDB [])],
        termAtom registeredOperatorAtom constants [] (source.toDB []), .symbol "HOL:Nil", .symbol "ASSUME"]]
       else .symbol "None") := by
  apply infer_captured_return bindings state _ _ _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_source_return state _ _ "ASSUME" assumeSelected _ (assume_selected _ _)
  apply source_body_return world table origins constants source resolved annotations type typed state axioms receipts cache
    "ASSUME" assumeSelected
  exact assume_selected_return world constants (source.toDB []) type
    ((DBTerm.inferType_toDB [] source).trans typed) formed booleanFormed _ state
    (by simp [applySubst, Subst.lookup, List.find?])

/-- The actual completed assumption computation accepts exactly the shared
HOL Boolean-term judgment. In particular, support of a formed term alone
does not suffice to introduce it as a hypothesis. -/
theorem authored_assume_accepts_iff (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (formed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]) :
    (∃ payload : Atom, (theory program).MultiStep
      { state, control := .evaluate bindings (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) }
      (finished state [.expression [.symbol "Some", payload]] [] [])) ↔ source.canonical.IsBool := by
  have returned := authored_infer_assume_return world table origins constants source.source resolved annotations
    source.ty source.checked formed booleanFormed bindings state axioms receipts cache stateKey requestKey
    stateCaptured requestCaptured
  have comparison : Ty.same source.ty Ty.bool = true ↔ source.canonical.IsBool := by
    exact Ty.same_eq_true_iff source.ty Ty.bool
  rw [← comparison]
  constructor
  · rintro ⟨payload, path⟩
    obtain ⟨firstFuel, first⟩ := path_has_sufficient_fuel program _ state _ [] [] path
    obtain ⟨secondFuel, second⟩ := pure_returns_has_sufficient_fuel program bindings state state _ _ returned
    have observed := completed_result_unique program firstFuel secondFuel _ state state
      _ [] [] _ [] [] first second
    have equal := List.singleton_inj.mp observed.2.1
    by_contra refused
    simp [refused] at equal
  · intro isBool
    refine ⟨.expression [.symbol "HOL:Thm", Premises.keys
      [termAtom registeredOperatorAtom constants [] source.canonical.term],
      termAtom registeredOperatorAtom constants [] source.canonical.term, .symbol "HOL:Nil", .symbol "ASSUME"], ?_⟩
    simpa only [CheckedSourceTerm.canonical, isBool, ↓reduceIte] using returned

/-- Reflexivity's actual source return realizes the existing shared rule and
has a derivation in every axiom policy. No source theorem name or selected
commitment is used as evidence. -/
theorem authored_refl_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source]) (policy : AxiomPolicy) :
    ∃ out : Theorem, InferenceRequest.Semantics (.refl source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
          termAtom registeredOperatorAtom constants [] out.sequent.concl.term, .symbol "HOL:Nil", .symbol "REFL"]]) := by
  let equality := CanonicalTerm.equalityOfSameType source.canonical source.canonical rfl
  let out := Theorem.emptyResult ∅ equality
  have semantics : ReflSemantics source.canonical out :=
    ⟨equality, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  have derivation := derives_of_nullary_check policy (.core (.refl source.canonical)) out rfl True.intro
    ((checkRefl_eq_some_iff source.canonical out).mpr semantics)
  refine ⟨out, semantics, derivation, rfl, rfl, ?_⟩
  exact authored_infer_refl_return world table origins constants equalityIdentity source.source resolved annotations
    source.ty source.checked bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured

/-- An admitted Boolean assumption realizes the existing shared rule while
retaining the one hypothesis and empty axiom dependencies in its source result. -/
theorem authored_assume_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (formed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (isBool : source.canonical.IsBool)
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "ASSUME", TermReading.sourceAtom source.source]) (policy : AxiomPolicy) :
    ∃ out : Theorem, InferenceRequest.Semantics (.assume source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = {source.canonical} ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", .expression [.symbol "HOL:Thm",
          Premises.keys [termAtom registeredOperatorAtom constants [] source.canonical.term],
          termAtom registeredOperatorAtom constants [] out.sequent.concl.term, .symbol "HOL:Nil", .symbol "ASSUME"]]) := by
  let out := Theorem.emptyResult {source.canonical} source.canonical
  have semantics : AssumeSemantics source.canonical out := ⟨isBool, rfl, rfl, rfl⟩
  have derivation := derives_of_nullary_check policy (.core (.assume source.canonical)) out rfl True.intro
    ((checkAssume_eq_some_iff source.canonical out).mpr semantics)
  refine ⟨out, semantics, derivation, rfl, rfl, ?_⟩
  have returned := authored_infer_assume_return world table origins constants source.source resolved annotations
    source.ty source.checked formed booleanFormed bindings state axioms receipts cache stateKey requestKey
    stateCaptured requestCaptured
  have accepted : Ty.same source.ty Ty.bool = true := (Ty.same_eq_true_iff source.ty Ty.bool).mpr isBool
  simpa only [CheckedSourceTerm.canonical, out, Theorem.emptyResult, accepted, ↓reduceIte] using returned

private theorem trans_selected (source first second : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "TRANS", first, second]))
      (.expression [.symbol "TRANS", first, second]) cases =
      some ([("second", second), ("first", first)] ++
        environment source (.expression [.symbol "TRANS", first, second]), transBody) := by
  have initialCases : cases =
      (.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2) ::
      (.expression [.symbol "TRANS", .var "first", .var "second"], transBody) :: cases.drop 2 := by decide
  rw [initialCases]
  simp [environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private def mkCombBody : Atom := .expression [.symbol "hol-light:mk-comb",
  .expression [.symbol "hol-light:known", .var "state", .var "first"],
  .expression [.symbol "hol-light:known", .var "state", .var "second"]]

private theorem mk_comb_selected (source first second : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "MK_COMB", first, second]))
      (.expression [.symbol "MK_COMB", first, second]) cases =
      some ([("second", second), ("first", first)] ++
        environment source (.expression [.symbol "MK_COMB", first, second]), mkCombBody) := by
  have initialCases : cases =
      (.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2) ::
      (.expression [.symbol "TRANS", .var "first", .var "second"], transBody) ::
      (.expression [.symbol "MK_COMB", .var "first", .var "second"], mkCombBody) :: cases.drop 3 := by decide
  rw [initialCases]
  simp [environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem dispatch_cached_return (state : State) (source first second : Atom) (kind : String)
    (selected answer : Atom)
    (selection : SpaceSemantics.selectCase (environment source (.expression [.symbol kind, first, second]))
      (.expression [.symbol kind, first, second]) cases =
      some ([("second", second), ("first", first)] ++
        environment source (.expression [.symbol kind, first, second]), selected))
    (returned : PureReturns program ([("second", second), ("first", first)] ++
      environment source (.expression [.symbol kind, first, second])) state selected state answer) :
    PureReturns program (environment source (.expression [.symbol kind, first, second])) state equation.body state answer := by
  rw [shape]
  apply case_returns program _ _ state state state (.var "request") (.expression [.symbol kind, first, second])
    selected _ _ cases (read_cases_encoded cases)
  · exact variable_returns program _ state "request"
  · exact selection
  · exact returned

/-- The actual dispatcher retrieves both equality premises in their source
order before performing application congruence. It retains the entire state
and constructs exactly the source hypothesis and dependency unions. -/
theorem authored_infer_mk_comb_return (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (domain codomain : Ty)
    (functionLeft functionRight argumentLeft argumentRight : DBTerm)
    (functionLeftChecked : functionLeft.inferType positions = some (.function domain codomain))
    (functionRightChecked : functionRight.inferType positions = some (.function domain codomain))
    (argumentLeftChecked : argumentLeft.inferType positions = some domain)
    (argumentRightChecked : argumentRight.inferType positions = some domain)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some (Transitivity.theoremValue constants positions (.function domain codomain)
      functionLeft functionRight hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some (Transitivity.theoremValue constants positions domain
      argumentLeft argumentRight hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "MK_COMB", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (.expression [.symbol "Some", Transitivity.theoremValue constants positions codomain
        (.app functionLeft argumentLeft) (.app functionRight argumentRight)
        (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "MK_COMB")]) := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "MK_COMB", first, second]
  let bound : Subst := [("second", second), ("first", first)] ++ environment source request
  apply infer_captured_return bindings state source request _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_cached_return state source first second "MK_COMB" mkCombBody _ (mk_comb_selected source first second)
  unfold mkCombBody
  apply Application.authored_mk_comb_computed_return constants equalityIdentity bound state positions domain codomain
    functionLeft functionRight argumentLeft argumentRight functionLeftChecked functionRightChecked
    argumentLeftChecked argumentRightChecked hyps1 hyps2 deps1 deps2 origin1 origin2
  · simpa only [firstFound, Lookup.answer] using
      ProofLookup.authored_known_return bound state operators declarations axioms receipts first cache "state" "first"
        (by simp [bound, source, request, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
  · simpa only [secondFound, Lookup.answer] using
      ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
        (by simp [bound, source, request, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])

/-- A missing premise key cannot be replaced with the other cached value or
with a theorem-shaped record supplied outside the actual proof lookup. -/
theorem authored_infer_mk_comb_missing_refused (bindings : Subst) (state : State)
    (operators declarations axioms receipts : Atom) (cache : List (Atom × Atom)) (first second : Atom)
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "MK_COMB", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "MK_COMB", first, second]
  let bound : Subst := [("second", second), ("first", first)] ++ environment source request
  apply infer_captured_return bindings state source request _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_cached_return state source first second "MK_COMB" mkCombBody _ (mk_comb_selected source first second)
  unfold mkCombBody
  apply Application.authored_mk_comb_missing_computed_return bound state _ _ (Lookup.answer (cache.lookup second))
  · exact ProofLookup.missing_proof_refused bound state operators declarations axioms receipts first cache "state" "first"
      (by simp [bound, source, request, environment, applySubst, Subst.lookup])
      (by simp [bound, applySubst, Subst.lookup]) missing
  · exact ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
      (by simp [bound, source, request, environment, applySubst, Subst.lookup])
      (by simp [bound, applySubst, Subst.lookup])

private def eqMpBody : Atom := .expression [.symbol "hol-light:eq-mp",
  .expression [.symbol "hol-light:known", .var "state", .var "first"],
  .expression [.symbol "hol-light:known", .var "state", .var "second"]]

private theorem eq_mp_selected (source first second : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "EQ_MP", first, second]))
      (.expression [.symbol "EQ_MP", first, second]) cases =
      some ([("second", second), ("first", first)] ++
        environment source (.expression [.symbol "EQ_MP", first, second]), eqMpBody) := by
  have initialCases : cases = cases.take 6 ++
      [(.expression [.symbol "EQ_MP", .var "first", .var "second"], eqMpBody)] ++ cases.drop 7 := by decide
  rw [initialCases]
  have preceding : cases.take 6 =
      [(.expression [.symbol "REFL", .var "term"], (cases[0]'(by decide)).2),
       (.expression [.symbol "TRANS", .var "first", .var "second"], transBody),
       (.expression [.symbol "MK_COMB", .var "first", .var "second"], mkCombBody),
       (.expression [.symbol "ABS", .var "variable", .var "premise"], (cases[3]'(by decide)).2),
       (.expression [.symbol "BETA", .var "term"], (cases[4]'(by decide)).2),
       (.expression [.symbol "ASSUME", .var "term"], (cases[5]'(by decide)).2)] := by decide
  rw [preceding]
  simp [environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The dispatcher computes equality modus ponens from its two actual cache
lookups, retaining the left-match and registered Boolean-carrier guards. -/
theorem authored_infer_eq_mp_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (rightType equalityType : Ty)
    (left right conclusion : DBTerm) (rightChecked : right.inferType positions = some rightType)
    (rightTypeFormed : TypeFormed world.signature rightType)
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (leftFormed : AnnotationsFormed world.signature left)
    (conclusionFormed : AnnotationsFormed world.signature conclusion)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions equalityType left right hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Representation.theoremAtom constants positions conclusion hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (if DBTerm.same left conclusion then
        if Ty.same rightType Ty.bool then EqualityModusPonens.result constants positions right hyps1 hyps2 deps1 deps2
        else .symbol "None"
       else .symbol "None") := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "EQ_MP", first, second]
  let bound : Subst := [("second", second), ("first", first)] ++ environment source request
  apply infer_captured_return bindings state source request _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_cached_return state source first second "EQ_MP" eqMpBody _ (eq_mp_selected source first second)
  unfold eqMpBody
  apply EqualityModusPonens.authored_eq_mp_computed_return world constants identified equalityIdentity bound state positions
    rightType equalityType left right conclusion rightChecked rightTypeFormed booleanFormed leftFormed conclusionFormed
    hyps1 hyps2 deps1 deps2 origin1 origin2
  · simpa only [firstFound, Lookup.answer] using
      ProofLookup.authored_known_return bound state operators declarations axioms receipts first cache "state" "first"
        (by simp [bound, source, request, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])
  · simpa only [secondFound, Lookup.answer] using
      ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
        (by simp [bound, source, request, environment, applySubst, Subst.lookup])
        (by simp [bound, applySubst, Subst.lookup])

/-- An absent equality key is refused before any theorem data can stand in for
that premise. The other lookup occurrence still executes. -/
theorem authored_infer_eq_mp_missing_refused (bindings : Subst) (state : State)
    (operators declarations axioms receipts : Atom) (cache : List (Atom × Atom)) (first second : Atom)
    (missing : cache.lookup first = none) (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state (.symbol "None") := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "EQ_MP", first, second]
  let bound : Subst := [("second", second), ("first", first)] ++ environment source request
  apply infer_captured_return bindings state source request _ stateKey requestKey stateCaptured requestCaptured
  apply dispatch_cached_return state source first second "EQ_MP" eqMpBody _ (eq_mp_selected source first second)
  unfold eqMpBody
  apply EqualityModusPonens.authored_eq_mp_missing_computed_return bound state _ _ (Lookup.answer (cache.lookup second))
  · exact ProofLookup.missing_proof_refused bound state operators declarations axioms receipts first cache "state" "first"
      (by simp [bound, source, request, environment, applySubst, Subst.lookup])
      (by simp [bound, applySubst, Subst.lookup]) missing
  · exact ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
      (by simp [bound, source, request, environment, applySubst, Subst.lookup])
      (by simp [bound, applySubst, Subst.lookup])

private theorem trans_body_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions type left middle1 hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Transitivity.theoremValue constants positions type middle2 right hyps2 deps2 origin2)) :
    PureReturns program
      (environment (ProofLookup.sourceState operators declarations axioms receipts cache)
        (.expression [.symbol "TRANS", first, second])) state equation.body state
      (if DBTerm.same middle1 middle2 then .expression [.symbol "Some",
        Transitivity.theoremValue constants positions type left right
          (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "TRANS")]
       else .symbol "None") := by
  let source := ProofLookup.sourceState operators declarations axioms receipts cache
  let request := Atom.expression [.symbol "TRANS", first, second]
  let before := environment source request
  let bound : Subst := [("second", second), ("first", first)] ++ before
  rw [shape]
  apply case_returns program before bound state state state (.var "request") request transBody _ _ cases
    (read_cases_encoded cases)
  · exact variable_returns program before state "request"
  · exact trans_selected source first second
  · unfold transBody
    apply Transitivity.authored_trans_computed_return world constants identified equalityIdentity bound state
      positions type left middle1 middle2 right leftChecked rightChecked firstFormed secondFormed
      hyps1 hyps2 deps1 deps2 origin1 origin2
    · simpa only [firstFound, Lookup.answer] using
        ProofLookup.authored_known_return bound state operators declarations axioms receipts first cache "state" "first"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])
    · simpa only [secondFound, Lookup.answer] using
        ProofLookup.authored_known_return bound state operators declarations axioms receipts second cache "state" "second"
          (by simp [bound, before, environment, source, applySubst, Subst.lookup])
          (by simp [bound, applySubst, Subst.lookup])

/-- The actual dispatcher obtains both premise occurrences from its retained
cache and performs source transitivity with exact metadata and no store effect. -/
theorem authored_infer_trans_return (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (bindings : Subst) (state : State) (positions : List Ty) (type : Ty) (left middle1 middle2 right : DBTerm)
    (leftChecked : left.inferType positions = some type)
    (rightChecked : right.inferType positions = some type)
    (firstFormed : SignatureFormation.AnnotationsFormed world.signature middle1)
    (secondFormed : SignatureFormation.AnnotationsFormed world.signature middle2)
    (hyps1 hyps2 deps1 deps2 : List Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some
      (Transitivity.theoremValue constants positions type left middle1 hyps1 deps1 origin1))
    (secondFound : cache.lookup second = some
      (Transitivity.theoremValue constants positions type middle2 right hyps2 deps2 origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "TRANS", first, second]) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (if DBTerm.same middle1 middle2 then .expression [.symbol "Some",
        Transitivity.theoremValue constants positions type left right
          (Transitivity.union hyps1 hyps2) (Transitivity.union deps1 deps2) (.symbol "TRANS")]
       else .symbol "None") := by
  apply authored_variable_call_returns program bindings
    (environment (ProofLookup.sourceState operators declarations axioms receipts cache)
      (.expression [.symbol "TRANS", first, second])) state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using
      clause (ProofLookup.sourceState operators declarations axioms receipts cache) (.expression [.symbol "TRANS", first, second])
  · exact trans_body_return world constants identified equalityIdentity state positions type left middle1 middle2 right
      leftChecked rightChecked firstFormed secondFormed hyps1 hyps2 deps1 deps2 origin1 origin2
      operators declarations axioms receipts cache first second firstFound secondFound

/-- Actual EQ_MP dispatch preserves the existing shared derivation when
its cached premises are admitted. Ordered metadata computes precisely the
hypothesis and axiom support of that derivation. This is rule closure, not
an assumption that an arbitrary cache has a valid insertion history. -/
theorem authored_eq_mp_shared_derivation (world : DefinitionAdapters.TheoryContext) (constants : Const → Atom)
    (identified : DeclarationTable.Identifies world constants)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (policy : AxiomPolicy) (equality premise : Theorem) (right : CanonicalTerm)
    (equalityDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) equality)
    (premiseDerives : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) premise)
    (rightBoolean : right.IsBool)
    (equalityShape : equality.sequent.concl.term =
      CanonicalTerm.equalityDB Ty.bool premise.sequent.concl.term right.term)
    (booleanFormed : TypeFormed world.signature Ty.bool)
    (premiseFormed : AnnotationsFormed world.signature premise.sequent.concl.term)
    (bindings : Subst) (state : State) (hyps1 hyps2 : List CanonicalTerm) (deps1 deps2 : List Sequent)
    (firstHypSupport : hyps1.toFinset = equality.sequent.hyp)
    (secondHypSupport : hyps2.toFinset = premise.sequent.hyp)
    (firstDepSupport : deps1.toFinset = equality.axioms)
    (secondDepSupport : deps2.toFinset = premise.axioms)
    (axiomAtom : Sequent → Atom) (origin1 origin2 operators declarations axioms receipts : Atom)
    (cache : List (Atom × Atom)) (first second : Atom)
    (firstFound : cache.lookup first = some (Representation.theoremAtom constants [] equality.sequent.concl.term
      (hyps1.map (TheoremMetadata.hypothesisAtom constants)) (deps1.map axiomAtom) origin1))
    (secondFound : cache.lookup second = some (Representation.theoremAtom constants [] premise.sequent.concl.term
      (hyps2.map (TheoremMetadata.hypothesisAtom constants)) (deps2.map axiomAtom) origin2))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators declarations axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) = .expression [.symbol "EQ_MP", first, second]) :
    ∃ out : Theorem, InferenceRequest.Semantics (.eqMp equality premise) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.sequent.concl = right ∧
      PureReturns program bindings state
        (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", Representation.theoremAtom constants [] out.sequent.concl.term
          (Transitivity.union (hyps1.map (TheoremMetadata.hypothesisAtom constants))
            (hyps2.map (TheoremMetadata.hypothesisAtom constants)))
          (Transitivity.union (deps1.map axiomAtom) (deps2.map axiomAtom)) (.symbol "EQ_MP")]) ∧
      (Transitivity.union (hyps1.map (TheoremMetadata.hypothesisAtom constants))
        (hyps2.map (TheoremMetadata.hypothesisAtom constants))).toFinset =
          out.sequent.hyp.image (TheoremMetadata.hypothesisAtom constants) ∧
      (Transitivity.union (deps1.map axiomAtom) (deps2.map axiomAtom)).toFinset =
          out.axioms.image axiomAtom := by
  have premiseBoolean : premise.sequent.concl.IsBool := (derives_isBool premiseDerives).1
  change premise.sequent.concl.ty = Ty.bool at premiseBoolean
  change right.ty = Ty.bool at rightBoolean
  let out := Theorem.unionResult equality premise (equality.sequent.hyp ∪ premise.sequent.hyp) right
  have view : CanonicalTerm.EqualityViewSemantics equality.sequent.concl premise.sequent.concl right :=
    ⟨premiseBoolean.trans rightBoolean.symm, by simpa only [premiseBoolean] using equalityShape⟩
  have semantics : InferenceRequest.Semantics (.eqMp equality premise) out :=
    ⟨premise.sequent.concl, right, view, rfl, rfl, rfl, rfl⟩
  have derives := InferenceRequest.Semantics.shared_derivation policy semantics (by
    intro input member
    simp only [InferenceRequest.premises, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact equalityDerives
    · exact premiseDerives)
  refine ⟨out, semantics, derives, rfl, ?_, ?_, ?_⟩
  · have checked : right.term.inferType [] = some Ty.bool := by
      simpa only [rightBoolean] using right.checked
    have firstEncoded : cache.lookup first = some (Transitivity.theoremValue constants [] Ty.bool
        premise.sequent.concl.term right.term (hyps1.map (TheoremMetadata.hypothesisAtom constants))
          (deps1.map axiomAtom) origin1) := by
      simpa only [equalityShape, Transitivity.theoremValue] using firstFound
    have returned := authored_infer_eq_mp_return world constants identified equalityIdentity bindings state [] Ty.bool Ty.bool
      premise.sequent.concl.term right.term premise.sequent.concl.term checked booleanFormed booleanFormed
      premiseFormed premiseFormed (hyps1.map (TheoremMetadata.hypothesisAtom constants))
      (hyps2.map (TheoremMetadata.hypothesisAtom constants)) (deps1.map axiomAtom) (deps2.map axiomAtom)
      origin1 origin2 operators declarations axioms receipts cache first second firstEncoded secondFound
      stateKey requestKey stateCaptured requestCaptured
    have same : DBTerm.same premise.sequent.concl.term premise.sequent.concl.term = true :=
      (DBTerm.same_eq_true_iff _ _).mpr rfl
    have isBool : Ty.same Ty.bool Ty.bool = true := (Ty.same_eq_true_iff _ _).mpr rfl
    simpa only [same, isBool, ↓reduceIte, EqualityModusPonens.result, out, Theorem.unionResult] using returned
  · simpa only [out, Theorem.unionResult, firstHypSupport, secondHypSupport] using
      TheoremMetadata.union_encoded_support (TheoremMetadata.hypothesisAtom constants) hyps1 hyps2
  · simpa only [out, Theorem.unionResult, firstDepSupport, secondDepSupport] using
      TheoremMetadata.union_encoded_support axiomAtom deps1 deps2

namespace Controls

private def proposition : CanonicalTerm :=
  ⟨.free ⟨Name.global "p", Ty.bool⟩, Ty.bool, by simp [DBTerm.inferType]⟩
private def otherProposition : CanonicalTerm :=
  ⟨.free ⟨Name.global "q", Ty.bool⟩, Ty.bool, by simp [DBTerm.inferType]⟩
private def reflexivity : Theorem := Theorem.emptyResult ∅
  (CanonicalTerm.equalityOfSameType proposition proposition rfl)
private def assumption : Theorem := Theorem.emptyResult {proposition} proposition
private def equalityKey : Atom := .symbol "equality-premise"
private def propositionKey : Atom := .symbol "proposition-premise"
private theorem keysDifferent : (propositionKey == equalityKey) = false := by decide
private def operators : Atom := OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators
  (fun _ => .symbol "HOL:Primitive")
private def declarations : Atom := DeclarationTable.tableAtom DeclarationTable.sourcePrimitive DeclarationTable.primitiveIdentity
private def cache : List (Atom × Atom) :=
  [(equalityKey, Transitivity.theoremValue DeclarationTable.primitiveIdentity [] Ty.bool proposition.term proposition.term
      [] [] (.symbol "REFL")),
   (propositionKey, Representation.theoremAtom DeclarationTable.primitiveIdentity [] proposition.term
      [TheoremMetadata.hypothesisAtom DeclarationTable.primitiveIdentity proposition] [] (.symbol "ASSUME"))]
private def captured : Subst :=
  [("request", .expression [.symbol "EQ_MP", equalityKey, propositionKey]),
   ("state", ProofLookup.sourceState operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") cache)]
private theorem boolean_formed : TypeFormed SourceProfile.primitiveContext.signature Ty.bool :=
  DefinitionAdapters.ContextControls.boolean_formed.mono
    (DefinitionAdapters.ContextControls.core_includes.trans
      (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))

/-- A concrete registered-profile instance derives p from reflexivity p=p
and assumption p. Its actual dispatcher returns the one retained hypothesis,
with no axiom dependencies. Both premise derivations are constructed here. -/
theorem reflexive_eq_mp_checked (state : State) :
    ∃ out : Theorem, Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out ∧
      out.sequent.concl = proposition ∧
      PureReturns program captured state
        (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
        (.expression [.symbol "Some", Representation.theoremAtom DeclarationTable.primitiveIdentity [] out.sequent.concl.term
          (Transitivity.union [] [TheoremMetadata.hypothesisAtom DeclarationTable.primitiveIdentity proposition])
          (Transitivity.union [] []) (.symbol "EQ_MP")]) := by
  have reflSemantics : ReflSemantics proposition reflexivity :=
    ⟨_, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  have reflDerives := derives_of_nullary_check emptyAxiomPolicy (.core (.refl proposition)) reflexivity rfl True.intro
    ((checkRefl_eq_some_iff _ _).mpr reflSemantics)
  have assumeSemantics : AssumeSemantics proposition assumption := ⟨rfl, rfl, rfl, rfl⟩
  have assumeDerives := derives_of_nullary_check emptyAxiomPolicy (.core (.assume proposition)) assumption rfl True.intro
    ((checkAssume_eq_some_iff _ _).mpr assumeSemantics)
  obtain ⟨out, -, derivation, conclusion, returned, -, -⟩ := authored_eq_mp_shared_derivation
    SourceProfile.primitiveContext DeclarationTable.primitiveIdentity
    (DeclarationTable.primitiveIdentity_identifies _) rfl emptyAxiomPolicy reflexivity assumption proposition
    reflDerives assumeDerives rfl rfl boolean_formed (.free boolean_formed)
    captured state [] [proposition] [] [] rfl rfl rfl rfl (fun _ => .symbol "unused-axiom")
    (.symbol "REFL") (.symbol "ASSUME") operators declarations (.symbol "HOL:Nil") (.symbol "HOL:Nil") cache
    equalityKey propositionKey
    (by simp [cache, equalityKey, propositionKey, reflexivity,
      CanonicalTerm.equalityOfSameType, Theorem.emptyResult, Transitivity.theoremValue, proposition])
    (by simp [List.lookup, cache, keysDifferent, assumption, Theorem.emptyResult]) "state" "request"
    (by simp [captured, applySubst, Subst.lookup]) (by simp [captured, applySubst, Subst.lookup])
  exact ⟨out, derivation, conclusion, returned⟩

private def mismatchedBindings : Subst :=
  [("second", .expression [.symbol "Some", Representation.theoremAtom DeclarationTable.primitiveIdentity []
      otherProposition.term [TheoremMetadata.hypothesisAtom DeclarationTable.primitiveIdentity otherProposition]
      [] (.symbol "ASSUME")]),
   ("first", .expression [.symbol "Some", Transitivity.theoremValue DeclarationTable.primitiveIdentity [] Ty.bool
      proposition.term proposition.term [] [] (.symbol "REFL")])]

/-- A typed Boolean premise q cannot replace p in p=p, even though its
carrier and record constructor agree. This is a concrete source refusal. -/
theorem mismatched_boolean_premise_refused (state : State) :
    PureReturns program mismatchedBindings state
      (.expression [.symbol "hol-light:eq-mp", .var "first", .var "second"]) state (.symbol "None") := by
  have returned := EqualityModusPonens.authored_eq_mp_computed_return SourceProfile.primitiveContext
    DeclarationTable.primitiveIdentity (DeclarationTable.primitiveIdentity_identifies _) rfl
    mismatchedBindings state [] Ty.bool Ty.bool proposition.term proposition.term otherProposition.term
    proposition.checked boolean_formed boolean_formed (.free boolean_formed) (.free boolean_formed)
    [] [TheoremMetadata.hypothesisAtom DeclarationTable.primitiveIdentity otherProposition] [] []
    (.symbol "REFL") (.symbol "ASSUME") (.var "first") (.var "second")
    (by simpa [mismatchedBindings, applySubst, Subst.lookup] using variable_returns program mismatchedBindings state "first")
    (by simpa [mismatchedBindings, applySubst, Subst.lookup] using variable_returns program mismatchedBindings state "second")
  have mismatch : DBTerm.same proposition.term otherProposition.term = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have equal := (DBTerm.same_eq_true_iff _ _).mp same
    simp [proposition, otherProposition, Name.global] at equal
  simpa only [mismatch, Bool.false_eq_true, ↓reduceIte] using returned

private def nonBoolean : CanonicalTerm :=
  ⟨.free ⟨Name.global "a", .var (Name.global "A")⟩, .var (Name.global "A"), by simp [DBTerm.inferType]⟩
private def nonBooleanBindings : Subst :=
  [("second", .expression [.symbol "Some", Representation.theoremAtom DeclarationTable.primitiveIdentity []
      nonBoolean.term [] [] (.symbol "unadmitted-record")]),
   ("first", .expression [.symbol "Some", Transitivity.theoremValue DeclarationTable.primitiveIdentity []
      nonBoolean.ty nonBoolean.term nonBoolean.term [] [] (.symbol "REFL")])]

/-- Matching raw records cannot manufacture a non-Boolean EQ_MP result.
Formation as data and a correct type annotation are insufficient admission. -/
theorem non_boolean_output_refused (state : State) :
    PureReturns program nonBooleanBindings state
      (.expression [.symbol "hol-light:eq-mp", .var "first", .var "second"]) state (.symbol "None") := by
  have formed : TypeFormed SourceProfile.primitiveContext.signature nonBoolean.ty := by
    simp [nonBoolean, TypeFormed]
  have returned := EqualityModusPonens.authored_eq_mp_computed_return SourceProfile.primitiveContext
    DeclarationTable.primitiveIdentity (DeclarationTable.primitiveIdentity_identifies _) rfl
    nonBooleanBindings state [] nonBoolean.ty nonBoolean.ty nonBoolean.term nonBoolean.term nonBoolean.term
    nonBoolean.checked formed boolean_formed (.free formed) (.free formed) [] [] [] []
    (.symbol "REFL") (.symbol "unadmitted-record") (.var "first") (.var "second")
    (by simpa [nonBooleanBindings, applySubst, Subst.lookup] using variable_returns program nonBooleanBindings state "first")
    (by simpa [nonBooleanBindings, applySubst, Subst.lookup] using variable_returns program nonBooleanBindings state "second")
  have same : DBTerm.same nonBoolean.term nonBoolean.term = true := (DBTerm.same_eq_true_iff _ _).mpr rfl
  have notBool : Ty.same nonBoolean.ty Ty.bool = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have equal := (Ty.same_eq_true_iff _ _).mp same
    simp [nonBoolean, Ty.bool] at equal
  simpa only [same, notBool, ↓reduceIte, Bool.false_eq_true] using returned

end Controls

end Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution
