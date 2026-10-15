import Mettapedia.Languages.HOLLight.MeTTa.BinderOpening
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution
import Mettapedia.Languages.OpenTheory.SourceBinding

/-!
# Executed source BETA

HOL Light's primitive accepts `(lambda v. body) v`, with the exact typed
variable as its argument. The actual source reader, positional opening and
theorem construction recover that named body. Arbitrary beta instances are
not admitted by this primitive; their construction requires substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Beta

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open Eval
open Effects (State boolean)
open Representation (termAtom registeredOperatorAtom)
open TypeSubstitution (typeAtom nameAtom)
open SignatureFormation

def redex (needle : SourceVar) (body : SourceTerm) : SourceTerm :=
  .app (.abs needle.name needle.ty body) (.var needle.name needle.ty)

theorem redex_typed (needle : SourceVar) (body : SourceTerm) (type : Ty)
    (typed : body.inferType = some type) : (redex needle body).inferType = some type := by
  simp [redex, SourceTerm.inferType, typed, Ty.destFunction?, Ty.function]

def result (constants : Const → Atom) (needle : SourceVar) (body : SourceTerm) (type : Ty) : Atom :=
  .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
    termAtom registeredOperatorAtom constants []
      (CanonicalTerm.equalityDB type ((redex needle body).toDB []) (body.toDB [])),
    .symbol "HOL:Nil", .symbol "BETA"]]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:beta"))[0]'(by decide)
private def resultBody : Atom := .expression [.symbol "hol-light:theorem-eq", .symbol "HOL:Nil",
  .expression [.symbol "HOL:App", .expression [.symbol "HOL:Lam", .var "domain", .var "value"], .var "arg"],
  .expression [.symbol "hol-light:open-binder", .var "arg", .grounded (.int 0), .var "value"],
  .symbol "HOL:Nil", .symbol "BETA"]
private def innerCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:App",
      .expression [.symbol "HOL:Lam", .var "domain", .var "value"], .var "arg"]], resultBody),
   (.var "malformed", .symbol "None")]
private def guardBody : Atom := .expression [.symbol "if",
  .expression [.symbol "==", .var "argument", .expression [.symbol "Var", .var "name", .var "type"]],
  .expression [.symbol "case", .expression [.symbol "hol-light:read", .var "state", .var "term"],
    .expression (innerCases.map fun row => .expression [row.1, row.2])], .symbol "None"]
private def outerCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Comb", .expression [.symbol "Abs",
      .expression [.symbol "Var", .var "name", .var "type"], .var "body"], .var "argument"], guardBody),
   (.var "malformed", .symbol "None")]
private def environment (source term : Atom) : Subst := [("term", term), ("state", source)]
private theorem shape : equation.body = .expression [.symbol "case", .var "term",
    .expression (outerCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem clause (source term : Atom) : clauses program "hol-light:beta" [source, term] =
    [.evaluate (environment source term) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:beta") = [equation] := by rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "term"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem body_returns (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (body : SourceTerm) (type : Ty) (typed : body.inferType = some type)
    (resolved : TermReading.SourceResolved world.signature (redex needle body))
    (annotations : AnnotationsFormed world.signature ((redex needle body).toDB []))
    (axioms receipts : Atom) (cache : List (Atom × Atom)) (state : State) :
    PureReturns program (environment
      (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table constants) axioms receipts cache)
      (TermReading.sourceAtom (redex needle body))) state equation.body state (result constants needle body type) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let raw := TermReading.sourceAtom (redex needle body)
  let before := environment source raw
  let matched := [("argument", TermReading.sourceAtom (.var needle.name needle.ty)),
    ("body", TermReading.sourceAtom body), ("type", typeAtom registeredOperatorAtom needle.ty),
    ("name", nameAtom needle.name)] ++ before
  let opened := [("arg", termAtom registeredOperatorAtom constants [] (.free needle)),
    ("value", termAtom registeredOperatorAtom constants [needle.ty] (body.toDB [needle])),
    ("domain", typeAtom registeredOperatorAtom needle.ty)] ++ matched
  have bodyChecked : (body.toDB [needle]).inferType [needle.ty] = some type :=
    (DBTerm.inferType_toDB [needle] body).trans typed
  have wholeChecked : ((redex needle body).toDB []).inferType [] = some type :=
    (DBTerm.inferType_toDB [] (redex needle body)).trans (redex_typed needle body type typed)
  have reducedChecked : (body.toDB []).inferType [] = some type :=
    (DBTerm.inferType_toDB [] body).trans typed
  rw [shape]
  apply case_returns program before matched state state state (.var "term") raw guardBody _ _ outerCases
    (read_cases_encoded outerCases)
  · exact variable_returns program before state "term"
  · simp [raw, redex, TermReading.sourceAtom, Representation.sourceVariableAtom, outerCases, matched, before, environment,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]
  · unfold guardBody
    apply if_returns program matched state state state _ (boolean true) _ _ _
    · apply native_binary_call_returns program matched state state state state "==" _ _
        (TermReading.sourceAtom (.var needle.name needle.ty))
        (TermReading.sourceAtom (.var needle.name needle.ty)) _
        (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
      · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "argument"
      · apply binary_constructor_returns program matched state state state "Var" (.var "name") (.var "type")
          (nameAtom needle.name) (typeAtom registeredOperatorAtom needle.ty) (by decide) (by decide)
        · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "name"
        · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "type"
      · simpa only [BEq.rfl] using StdLib.structural_equality state
          (TermReading.sourceAtom (.var needle.name needle.ty)) (TermReading.sourceAtom (.var needle.name needle.ty))
    · simp only [boolean]
      apply case_returns program matched opened state state state _
        (.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] ((redex needle body).toDB [])])
        resultBody _ _ innerCases (read_cases_encoded innerCases)
      · exact InferenceExecution.authored_state_read_return world table origins constants (redex needle body) resolved
          annotations type (redex_typed needle body type typed) matched state axioms receipts cache "state" "term"
          (by simp [matched, before, environment, source, applySubst, Subst.lookup])
          (by simp [matched, before, environment, raw, applySubst, Subst.lookup])
      · simp [innerCases, opened, matched, before, environment, redex, SourceTerm.toDB, boundIndex, termAtom,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup]
      · unfold resultBody result
        apply Equality.authored_theorem_equality_computed_return constants opened state []
          ((redex needle body).toDB []) (body.toDB []) type wholeChecked reducedChecked equalityIdentity
          (.symbol "HOL:Nil") (.symbol "HOL:Nil") (.symbol "BETA") _ _ _ _ _
        · exact symbol_returns program opened state "HOL:Nil"
        · simp only [redex, SourceTerm.toDB, boundIndex, termAtom]
          apply binary_constructor_returns program opened state state state "HOL:App" _ _ _ _ (by decide) (by decide)
          · apply binary_constructor_returns program opened state state state "HOL:Lam" _ _ _ _ (by decide) (by decide)
            · simpa [opened, applySubst, Subst.lookup] using variable_returns program opened state "domain"
            · simpa [opened, applySubst, Subst.lookup] using variable_returns program opened state "value"
          · simpa [opened, applySubst, Subst.lookup, redex, SourceTerm.toDB, boundIndex, termAtom] using
              variable_returns program opened state "arg"
        · have returned := BinderOpening.authored_open_computed_return registeredOperatorAtom constants
            (CheckedSourceTerm.ofVariable needle).canonical (body.toDB [needle]) [] type bodyChecked
            opened state (.var "arg") (.grounded (.int 0)) (.var "value")
            (by simpa [opened, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB,
              boundIndex, applySubst, Subst.lookup] using variable_returns program opened state "arg")
            (grounded_returns program opened state (.int 0))
            (by simpa [opened, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, applySubst, Subst.lookup]
              using variable_returns program opened state "value")
          simpa only [CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB,
            boundIndex, List.length_nil, List.nil_append, SourceTerm.instantiateAt_toDB_singleton] using returned
        · exact symbol_returns program opened state "HOL:Nil"
        · exact symbol_returns program opened state "BETA"

/-- The source primitive executes its own named-variable guard and registered
reader. Its result is equality with the original named body, with no added
hypothesis or axiom dependency. The cache and receipts are not changed. -/
theorem authored_beta_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (body : SourceTerm) (type : Ty) (typed : body.inferType = some type)
    (resolved : TermReading.SourceResolved world.signature (redex needle body))
    (annotations : AnnotationsFormed world.signature ((redex needle body).toDB []))
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey termKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (termCaptured : applySubst bindings (.var termKey) = TermReading.sourceAtom (redex needle body)) :
    PureReturns program bindings state (.expression [.symbol "hol-light:beta", .var stateKey, .var termKey]) state
      (result constants needle body type) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let raw := TermReading.sourceAtom (redex needle body)
  apply authored_variable_call_returns program bindings (environment source raw) state state "hol-light:beta" [stateKey, termKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, termCaptured] using clause source raw
  · exact body_returns world table origins constants equalityIdentity needle body type typed resolved annotations axioms receipts cache state

/-- A differently encoded argument is refused before invoking the reader.
No alleged signature, cache entry or theorem origin bypasses this guard. -/
theorem authored_beta_wrong_argument_refused (needle : SourceVar) (body argument source : Atom)
    (different : argument ≠ Representation.sourceVariableAtom registeredOperatorAtom needle)
    (bindings : Subst) (state : State) (stateKey termKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (termCaptured : applySubst bindings (.var termKey) = .expression [.symbol "Comb",
      .expression [.symbol "Abs", Representation.sourceVariableAtom registeredOperatorAtom needle, body], argument]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:beta", .var stateKey, .var termKey]) state
      (.symbol "None") := by
  let raw := Atom.expression [.symbol "Comb",
    .expression [.symbol "Abs", Representation.sourceVariableAtom registeredOperatorAtom needle, body], argument]
  let before := environment source raw
  let matched := [("argument", argument), ("body", body),
    ("type", typeAtom registeredOperatorAtom needle.ty), ("name", nameAtom needle.name)] ++ before
  apply authored_variable_call_returns program bindings before state state "hol-light:beta" [stateKey, termKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, termCaptured] using clause source raw
  · rw [shape]
    apply case_returns program before matched state state state (.var "term") raw guardBody _ _ outerCases
      (read_cases_encoded outerCases)
    · exact variable_returns program before state "term"
    · simp [raw, outerCases, matched, before, environment, Representation.sourceVariableAtom,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup]
    · unfold guardBody
      apply if_returns program matched state state state _ (boolean false) _ _ _
      · apply native_binary_call_returns program matched state state state state "==" _ _ argument
          (Representation.sourceVariableAtom registeredOperatorAtom needle) _
          (by decide) (by decide) (by decide) (by decide) _ _ _ (by decide)
        · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "argument"
        · apply binary_constructor_returns program matched state state state "Var" (.var "name") (.var "type")
            (nameAtom needle.name) (typeAtom registeredOperatorAtom needle.ty) (by decide) (by decide)
          · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "name"
          · simpa [matched, applySubst, Subst.lookup] using variable_returns program matched state "type"
        · have comparison : (argument == Representation.sourceVariableAtom registeredOperatorAtom needle) = false :=
            Bool.eq_false_of_not_eq_true (fun equal => different (Atom.eq_of_beq_eq_true equal))
          simpa only [comparison] using StdLib.structural_equality state argument
            (Representation.sourceVariableAtom registeredOperatorAtom needle)
      · simpa [boolean] using symbol_returns program matched state "None"

/-- Equal spelling at a different formed type is still a different source
variable. The actual primitive refuses it, rather than treating it as BETA. -/
theorem authored_beta_different_variable_refused (world : DefinitionAdapters.TheoryContext)
    (needle argument : SourceVar) (needleFormed : TypeFormed world.signature needle.ty)
    (argumentFormed : TypeFormed world.signature argument.ty) (different : argument ≠ needle)
    (body source : Atom) (bindings : Subst) (state : State) (stateKey termKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = source)
    (termCaptured : applySubst bindings (.var termKey) = .expression [.symbol "Comb",
      .expression [.symbol "Abs", Representation.sourceVariableAtom registeredOperatorAtom needle, body],
      Representation.sourceVariableAtom registeredOperatorAtom argument]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:beta", .var stateKey, .var termKey]) state
      (.symbol "None") :=
  authored_beta_wrong_argument_refused needle body _ source
    (fun same => different ((Representation.registered_sourceVariableAtom_eq_iff world argument needle
      argumentFormed needleFormed).mp same)) bindings state stateKey termKey stateCaptured termCaptured

namespace Dispatcher

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:infer"))[0]'(by decide)
private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "hol-light:beta", .var "state", .var "term"]
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
private theorem selection (source raw : Atom) :
    SpaceSemantics.selectCase (environment source (.expression [.symbol "BETA", raw]))
      (.expression [.symbol "BETA", raw]) cases =
      some (("term", raw) :: environment source (.expression [.symbol "BETA", raw]), selected) := by
  have initial : cases = (cases[0]'(by decide)) :: (cases[1]'(by decide)) :: (cases[2]'(by decide)) ::
      (cases[3]'(by decide)) :: (.expression [.symbol "BETA", .var "term"], selected) :: cases.drop 5 := by decide
  have first : (cases[0]'(by decide)).1 = .expression [.symbol "REFL", .var "term"] := by decide
  have second : (cases[1]'(by decide)).1 = .expression [.symbol "TRANS", .var "first", .var "second"] := by decide
  have third : (cases[2]'(by decide)).1 = .expression [.symbol "MK_COMB", .var "first", .var "second"] := by decide
  have fourth : (cases[3]'(by decide)).1 = .expression [.symbol "ABS", .var "variable", .var "premise"] := by decide
  rw [initial]
  simp only [SpaceSemantics.selectCase, first, second, third, fourth]
  simp [environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The actual BETA request dispatches to the guarded source primitive rather
than admitting a general canonical beta redex directly. -/
theorem authored_infer_beta_return (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (body : SourceTerm) (type : Ty) (typed : body.inferType = some type)
    (resolved : TermReading.SourceResolved world.signature (redex needle body))
    (annotations : AnnotationsFormed world.signature ((redex needle body).toDB []))
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "BETA", TermReading.sourceAtom (redex needle body)]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
      (result constants needle body type) := by
  let source := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms receipts cache
  let raw := TermReading.sourceAtom (redex needle body)
  let request := Atom.expression [.symbol "BETA", raw]
  let before := environment source request
  let bound := ("term", raw) :: before
  apply authored_variable_call_returns program bindings before state state "hol-light:infer" [stateKey, requestKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, requestCaptured] using clause source request
  · rw [shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ cases
      (read_cases_encoded cases)
    · exact variable_returns program before state "request"
    · exact selection source raw
    · exact authored_beta_return world table origins constants equalityIdentity needle body type typed resolved annotations
        bound state axioms receipts cache "state" "term"
        (by simp [bound, before, environment, source, applySubst, Subst.lookup])
        (by simp [bound, raw, applySubst, Subst.lookup])

end Dispatcher

/-- Executing the source BETA request earns an actual shared HOL derivation
with the source rule's restriction and the original named body as its right
operand. This result uses no cached premise, hypothesis or axiom dependency. -/
theorem authored_beta_shared_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (needle : SourceVar) (body : CheckedSourceTerm)
    (resolved : TermReading.SourceResolved world.signature (redex needle body.source))
    (annotations : AnnotationsFormed world.signature ((redex needle body.source).toDB []))
    (bindings : Subst) (state : State) (axioms receipts : Atom) (cache : List (Atom × Atom))
    (stateKey requestKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms receipts cache)
    (requestCaptured : applySubst bindings (.var requestKey) =
      .expression [.symbol "BETA", TermReading.sourceAtom (redex needle body.source)]) (policy : AxiomPolicy) :
    ∃ (source : CheckedSourceTerm) (out : Theorem), source.source = redex needle body.source ∧
      SourceBetaSemantics source out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧
      out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl.term = CanonicalTerm.equalityDB body.ty
        ((redex needle body.source).toDB []) (body.source.toDB []) ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:infer", .var stateKey, .var requestKey]) state
        (.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
          termAtom registeredOperatorAtom constants [] out.sequent.concl.term, .symbol "HOL:Nil", .symbol "BETA"]]) := by
  let source : CheckedSourceTerm := ⟨redex needle body.source, body.ty, redex_typed needle body.source body.ty body.checked⟩
  let equality := CanonicalTerm.equalityOfSameType source.canonical body.canonical rfl
  let out := Theorem.emptyResult ∅ equality
  have reduction : CanonicalTerm.BetaReductionSemantics source.canonical body.canonical := by
    refine ⟨needle.ty, body.source.toDB [needle], (CheckedSourceTerm.ofVariable needle).canonical, ?_, ?_⟩
    · simp [source, redex, CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable, SourceTerm.toDB, boundIndex]
    · simpa only [CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable, SourceTerm.toDB, boundIndex]
        using (SourceTerm.instantiateAt_toDB_singleton body.source needle).symm
  have semantics : SourceBetaSemantics source out :=
    ⟨by simp [source, redex, TrivialBetaRedex],
      ⟨body.canonical, equality, reduction,
        CanonicalTerm.equalityOfSameType_semantics source.canonical body.canonical rfl, rfl, rfl, rfl⟩⟩
  refine ⟨source, out, rfl, semantics, semantics.derivation_preservation policy, rfl, rfl, rfl, ?_⟩
  exact Dispatcher.authored_infer_beta_return world table origins constants equalityIdentity needle body.source body.ty
    body.checked resolved annotations bindings state axioms receipts cache stateKey requestKey stateCaptured requestCaptured

end Mettapedia.Languages.HOLLight.MeTTa.Beta
