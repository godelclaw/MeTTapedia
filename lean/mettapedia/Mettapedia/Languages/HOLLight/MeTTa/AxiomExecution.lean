import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorization

/-!
# Actual selected-commitment execution in the authored HOL checker

The source retrieves one named commitment, reads both formulas in the same
registered declaration context, compares them and checks the Boolean carrier.
Its axiom dependency is retained separately from proof-premise occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.AxiomExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval
open Effects (State boolean)
open Representation (registeredOperatorAtom termAtom)

private def equation : SpaceSemantics.Equation :=
  (definitionsSource.program.equations.filter (fun row => row.head == "hol-light:axiom"))[0]'(by decide)
private def resultBody : Atom := .expression [.symbol "Some", .expression [.symbol "HOL:Thm", .symbol "HOL:Nil",
  .var "term", .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:AxiomDependency", .var "name", .var "term"],
    .symbol "HOL:Nil"], .symbol "AXIOM"]]
private def selected : Atom := .expression [.symbol "if", .expression [.symbol "==", .var "term", .var "expected"],
  .expression [.symbol "if", .expression [.symbol "==", .expression [.symbol "hol-light:term-type", .var "term"],
    .expression [.symbol "Some", .expression [.symbol "hol-light:bool"]]], resultBody, .symbol "None"], .symbol "None"]
private def readCases : SpaceSemantics.Cases :=
  [(.expression [.expression [.symbol "Some", .var "term"], .expression [.symbol "Some", .var "expected"]], selected),
    (.var "malformed", .symbol "None")]
private def readBody : Atom := .expression [.symbol "case", .expression [
  .expression [.symbol "hol-light:read", .var "state", .var "source"],
  .expression [.symbol "hol-light:read", .var "state", .var "commitment"]],
  .expression (readCases.map fun row => .expression [row.1,row.2])]
private def commitmentCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .var "commitment"], readBody), (.var "undeclared", .symbol "None")]
private def commitmentBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "name", .var "axioms"],
  .expression (commitmentCases.map fun row => .expression [row.1,row.2])]
private def stateCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms", .var "cache", .var "receipts"],
    commitmentBody), (.var "malformed", .symbol "None")]
private def environment (sourceState label source : Atom) : Subst :=
  [("source", source), ("name", label), ("state", sourceState)]
private def stateEnvironment (operators constants label source receipts : Atom)
    (commitments cache : List (Atom × Atom)) : Subst :=
  [("receipts", receipts), ("cache", Lookup.table cache), ("axioms", Lookup.table commitments),
    ("constants", constants), ("operators", operators)] ++
    environment (ProofLookup.sourceState operators constants (Lookup.table commitments) receipts cache) label source
private theorem shape : equation.body = .expression [.symbol "case", .var "state",
    .expression (stateCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem clause (sourceState label source : Atom) :
    clauses program "hol-light:axiom" [sourceState,label,source] =
      [.evaluate (environment sourceState label source) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:axiom") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "name", .var "source"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

def result (constants : Const → Atom) (label : Atom) (source expected : CheckedSourceTerm) : Atom :=
  if DBTerm.same source.canonical.term expected.canonical.term then
    if Ty.same source.ty Ty.bool then
      .expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
        (termAtom registeredOperatorAtom constants [] source.canonical.term)
        (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
          termAtom registeredOperatorAtom constants [] source.canonical.term]]) (.symbol "AXIOM")]
    else .symbol "None"
  else .symbol "None"

private theorem body_certificate (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source)) (state : State) :
    BoundCalls.CorePath.PureReturns program
      (environment (ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table constants) (Lookup.table commitments) receipts cache)
        label (TermReading.sourceAtom source.source)) state equation.body state (result constants label source expected) := by
  have falseTest : (boolean false == boolean true) = false := by decide
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let before := environment (ProofLookup.sourceState operators declarations (Lookup.table commitments) receipts cache)
    label (TermReading.sourceAtom source.source)
  let worldBound := stateEnvironment operators declarations label (TermReading.sourceAtom source.source) receipts commitments cache
  let commitmentBound : Subst := ("commitment", TermReading.sourceAtom expected.source) :: worldBound
  let readBound : Subst := [("expected", termAtom registeredOperatorAtom constants [] expected.canonical.term),
    ("term", termAtom registeredOperatorAtom constants [] source.canonical.term)] ++ commitmentBound
  rw [shape]
  apply BoundCalls.CorePath.case_returns program before worldBound state state state (.var "state")
    (ProofLookup.sourceState operators declarations (Lookup.table commitments) receipts cache)
    commitmentBody _ _ stateCases (read_cases_encoded stateCases)
  · exact BoundCalls.CorePath.variable_returns program before state "state"
  · simp [stateCases, worldBound, before, stateEnvironment, environment, ProofLookup.sourceState,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  · unfold commitmentBody
    apply BoundCalls.CorePath.case_returns program worldBound commitmentBound state state state _
      (.expression [.symbol "Some", TermReading.sourceAtom expected.source]) readBody _ _ commitmentCases
      (read_cases_encoded commitmentCases)
    · simpa only [found, Lookup.answer] using Lookup.authored_lookup_certificate worldBound state label commitments "name" "axioms"
        (by simp [worldBound, stateEnvironment, environment, applySubst, Subst.lookup])
        (by simp [worldBound, stateEnvironment, applySubst, Subst.lookup])
    · simp [commitmentCases, commitmentBound, worldBound, stateEnvironment, environment, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold readBody
      apply BoundCalls.CorePath.case_returns program commitmentBound readBound state state state _
        (.expression [.expression [.symbol "Some", termAtom registeredOperatorAtom constants [] source.canonical.term],
          .expression [.symbol "Some", termAtom registeredOperatorAtom constants [] expected.canonical.term]]) selected
        _ _ readCases (read_cases_encoded readCases)
      · refine .step rfl (step_transition rfl) ?_
        apply BoundCalls.CorePath.arguments_return program commitmentBound state _ _ _ [] 0
        refine .cons ?_ (.cons ?_ .nil)
        · exact InferenceExecution.authored_state_read_certificate world table origins constants source.source sourceResolved
            sourceFormed source.ty source.checked commitmentBound state (Lookup.table commitments) receipts cache "state" "source" rfl rfl
        · exact InferenceExecution.authored_state_read_certificate world table origins constants expected.source expectedResolved
            expectedFormed expected.ty expected.checked commitmentBound state (Lookup.table commitments) receipts cache
            "state" "commitment" rfl rfl
      · simp [readCases, readBound, commitmentBound, worldBound, stateEnvironment, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold selected
        apply BoundCalls.CorePath.if_returns program readBound state state state _
          (boolean (DBTerm.same source.canonical.term expected.canonical.term)) _ _ _
        · exact Equality.authored_term_equality_test_certificate world constants identified readBound state []
            source.canonical.term expected.canonical.term sourceFormed expectedFormed "term" "expected" rfl rfl
        · cases compared : DBTerm.same source.canonical.term expected.canonical.term
          · simp only [result, compared, Bool.false_eq_true, ↓reduceIte]
            simpa only [falseTest, Bool.false_eq_true, ↓reduceIte] using BoundCalls.CorePath.symbol_returns program readBound state "None"
          · simp only [result, compared, ↓reduceIte, boolean, BEq.rfl]
            apply BoundCalls.CorePath.if_returns program readBound state state state _ (boolean (Ty.same source.ty Ty.bool)) _ _ _
            · exact Equality.authored_boolean_test_certificate world constants readBound state [] source.canonical.term source.ty
                source.canonical.checked sourceTypeFormed booleanFormed "term" rfl
            · cases Ty.same source.ty Ty.bool
              · simp only [Bool.false_eq_true, ↓reduceIte]
                simpa only [falseTest, Bool.false_eq_true, ↓reduceIte] using BoundCalls.CorePath.symbol_returns program readBound state "None"
              · simp only [↓reduceIte, boolean, BEq.rfl]
                unfold resultBody Publication.value Premises.keys
                apply BoundCalls.CorePath.unary_constructor_of_returns program readBound state state "Some" _ _ (by decide) (by decide)
                apply BoundCalls.CorePath.constructor_return program readBound state "HOL:Thm" _ _ (by decide) (by decide)
                refine .cons (BoundCalls.CorePath.symbol_returns program readBound state "HOL:Nil") (.cons ?_ (.cons ?_ (.cons
                  (BoundCalls.CorePath.symbol_returns program readBound state "AXIOM") .nil)))
                · exact BoundCalls.CorePath.variable_returns program readBound state "term"
                · apply BoundCalls.CorePath.constructor_return program readBound state "HOL:Cons" _ _ (by decide) (by decide)
                  refine .cons ?_ (.cons (BoundCalls.CorePath.symbol_returns program readBound state "HOL:Nil") .nil)
                  apply BoundCalls.CorePath.constructor_return program readBound state "HOL:AxiomDependency" _ _ (by decide) (by decide)
                  exact .cons (BoundCalls.CorePath.variable_returns program readBound state "name")
                    (.cons (BoundCalls.CorePath.variable_returns program readBound state "term") .nil)

/-- Actual selected-commitment execution classifies both formula equality and
the Boolean carrier guard. The lookup is ordered and both source reads run. -/
theorem authored_axiom_computed_certificate (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source.source) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (result constants label source expected) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment _ label (TermReading.sourceAtom source.source))
    state state "hol-light:axiom" [stateKey,labelKey,sourceKey] equation.body _
    (by decide) (by decide) (by decide) _
    (body_certificate world table origins constants identified source expected sourceResolved expectedResolved sourceFormed expectedFormed
      sourceTypeFormed booleanFormed label receipts commitments cache found state) (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, labelCaptured, sourceCaptured] using clause _ label (TermReading.sourceAtom source.source)

theorem authored_axiom_computed_return (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source.source) :
    PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (result constants label source expected) :=
  (authored_axiom_computed_certificate world table origins constants identified source expected sourceResolved expectedResolved
    sourceFormed expectedFormed sourceTypeFormed booleanFormed label receipts commitments cache found
    bindings state stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured).original

theorem authored_axiom_computed_bound_return (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source.source) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (result constants label source expected) :=
  (authored_axiom_computed_certificate world table origins constants identified source expected sourceResolved expectedResolved
    sourceFormed expectedFormed sourceTypeFormed booleanFormed label receipts commitments cache found
    bindings state stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured).extended

/-- The missing-commitment path is certified before either reader runs. No
typing, axiom-policy or derivation premise is needed for the arbitrary payload. -/
theorem authored_axiom_missing_certificate (operators constants label source receipts : Atom)
    (commitments cache : List (Atom × Atom)) (missing : commitments.lookup label = none)
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = source) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (.symbol "None") := by
  let before := environment (ProofLookup.sourceState operators constants (Lookup.table commitments) receipts cache) label source
  let bound := stateEnvironment operators constants label source receipts commitments cache
  let refused : Subst := ("undeclared", Atom.symbol "None") :: bound
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings before state state "hol-light:axiom" [stateKey,labelKey,sourceKey]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, labelCaptured, sourceCaptured] using clause _ label source
  · rw [shape]
    apply BoundCalls.CorePath.case_returns program before bound state state state (.var "state")
      (ProofLookup.sourceState operators constants (Lookup.table commitments) receipts cache)
      commitmentBody _ _ stateCases (read_cases_encoded stateCases)
    · exact BoundCalls.CorePath.variable_returns program before state "state"
    · simp [stateCases, bound, before, stateEnvironment, environment, ProofLookup.sourceState,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold commitmentBody
      apply BoundCalls.CorePath.case_returns program bound refused state state state _ (.symbol "None") (.symbol "None")
        _ _ commitmentCases (read_cases_encoded commitmentCases)
      · simpa only [missing, Lookup.answer] using Lookup.authored_lookup_certificate bound state label commitments "name" "axioms" rfl rfl
      · simp [commitmentCases, refused, bound, stateEnvironment, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, matchAtom, Subst.lookup]
      · exact BoundCalls.CorePath.symbol_returns program refused state "None"

/-- Missing commitments are refused in the original execution fragment before
either term reader runs, while retaining the complete store. -/
theorem authored_axiom_missing_return (operators constants label source receipts : Atom)
    (commitments cache : List (Atom × Atom)) (missing : commitments.lookup label = none)
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = source) :
    PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (.symbol "None") :=
  (authored_axiom_missing_certificate operators constants label source receipts commitments cache missing
    bindings state stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured).original

/-- The same constructed path also refuses the commitment in the captured-call
machine. No whole-checker soundness or evaluator-agreement premise is supplied. -/
theorem authored_axiom_missing_bound_return (operators constants label source receipts : Atom)
    (commitments cache : List (Atom × Atom)) (missing : commitments.lookup label = none)
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = source) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
      state (.symbol "None") :=
  (authored_axiom_missing_certificate operators constants label source receipts commitments cache missing
    bindings state stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured).extended

def dependency (label : Atom) (source : CheckedSourceTerm) (isBool : source.canonical.IsBool) : CacheAuthorization.Dependency :=
  ⟨label, source.canonical, isBool⟩
def record (label : Atom) (source : CheckedSourceTerm) (isBool : source.canonical.IsBool) : CacheAuthorization.Record :=
  ⟨[], source.canonical, [dependency label source isBool], .symbol "AXIOM"⟩

/-- The exact returned record earns a registered axiom derivation only under
the selected object-theory commitment. This introduces no host axiom. -/
theorem record_derived (policy : AxiomPolicy) (world : TheoryContext) (label : Atom)
    (source : CheckedSourceTerm) (isBool : source.canonical.IsBool)
    (formed : AnnotationsFormed world.signature source.canonical.term)
    (authorized : policy (dependency label source isBool).sequent) :
    TheoryDerives policy world (record label source isBool).fact := by
  apply TheoryDerives.axiom (sequent := (dependency label source isBool).sequent) rfl authorized
  · refine ⟨⟨isBool, by simp [dependency, CacheAuthorization.Dependency.sequent]⟩, ?_⟩
    simp [HasParts, record, dependency, CacheAuthorization.Record.fact, CacheAuthorization.Dependency.sequent]
  · refine ⟨⟨formed, ?_⟩, ?_⟩
    · simp [record, CacheAuthorization.Record.fact]
    · intro sequent member
      have same : sequent = (dependency label source isBool).sequent := by
        simpa [record, CacheAuthorization.Record.fact] using member
      subst sequent
      exact ⟨formed, by simp [dependency, CacheAuthorization.Dependency.sequent]⟩

/-- A successful actual commitment read and its registered derivation retain
the same formula and explicit dependency label. The policy premise is an
object-theory authorization, not an assumed checker-soundness interface. -/
theorem authored_axiom_derivation (policy : AxiomPolicy) (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm) (same : source.canonical = expected.canonical)
    (isBool : source.canonical.IsBool)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (label receipts : Atom) (commitments cache : List (Atom × Atom))
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (authorized : policy (dependency label source isBool).sequent)
    (bindings : Subst) (state : State) (stateKey labelKey sourceKey : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) receipts cache)
    (labelCaptured : applySubst bindings (.var labelKey) = label)
    (sourceCaptured : applySubst bindings (.var sourceKey) = TermReading.sourceAtom source.source) :
    TheoryDerives policy world (record label source isBool).fact ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:axiom", .var stateKey, .var labelKey, .var sourceKey])
        state (.expression [.symbol "Some", (record label source isBool).atom constants]) := by
  have returned := authored_axiom_computed_return world table origins constants identified source expected sourceResolved expectedResolved
    sourceFormed expectedFormed sourceTypeFormed booleanFormed label receipts commitments cache found bindings state
    stateKey labelKey sourceKey stateCaptured labelCaptured sourceCaptured
  refine ⟨record_derived policy world label source isBool sourceFormed authorized, ?_⟩
  have termsSame : source.canonical.term = expected.canonical.term := congrArg CanonicalTerm.term same
  have carrier : source.ty = Ty.bool := isBool
  simpa [result, DBTerm.same_eq_true_iff, termsSame, Ty.same_eq_true_iff, carrier, record, dependency,
    CacheAuthorization.Record.atom, CacheAuthorization.Dependency.atom, TheoremMetadata.hypothesisAtom,
    Representation.theoremAtom, Publication.value, Premises.keys] using returned

end Mettapedia.Languages.HOLLight.MeTTa.AxiomExecution
