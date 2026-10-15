import Mettapedia.Languages.HOLLight.MeTTa.AxiomExecution
import Mettapedia.Languages.MeTTa.PeTTa.BoundCallComposition

/-!
# Actual AXIOM dispatch to the captured authored helper

The source dispatcher selects its AXIOM arm, captures the helper's name and
enters the existing argument machine. Its publication continuation retains
the exact source state, event key and command. The complete path
reads the selected commitment, checks formula equality and the Boolean carrier,
then either publishes the exact payload or refuses the event. Logical
authorization remains separate from these source execution laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.AxiomDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval (Configuration Control Frame finished withFrames)
open Effects (State)
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Representation (registeredOperatorAtom termAtom)

def request (label source : Atom) : Atom := .expression [.symbol "AXIOM", label, source]

def capturedCall : Atom := .expression [.var "extension", .var "state", .var "name", .var "term"]

def publicationCall : Atom := .expression
  [.symbol "hol-light:publish", .var "state", .var "key", .var "request", capturedCall]

def arm : Atom := ProofEvents.dispatchCases[4].2

def environment (world key label source : Atom) : Subst :=
  [("term", source), ("name", label)] ++ ProofEvents.environment world key (request label source)

def capturedEnvironment (world key label source : Atom) : Subst :=
  ("extension", .symbol "hol-light:axiom") :: environment world key label source

theorem arm_shape : arm =
    .expression [.symbol "let", .var "extension", .symbol "hol-light:axiom", publicationCall] := by decide

theorem selected (world key label source : Atom) :
    SpaceSemantics.selectCase (ProofEvents.environment world key (request label source))
      (request label source) ProofEvents.dispatchCases =
      some (environment world key label source, arm) := by
  have rows : ProofEvents.dispatchCases =
      [(.expression [.symbol "DECLARE_TYPE", .var "name", .var "arity"], ProofEvents.dispatchCases[0].2),
       (.expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], ProofEvents.dispatchCases[1].2),
       (.expression [.symbol "DEFINITION", .var "name", .var "schema", .var "body"], ProofEvents.dispatchCases[2].2),
       (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], ProofEvents.dispatchCases[3].2),
       (.expression [.symbol "AXIOM", .var "name", .var "term"], arm),
       (.var "inference", ProofEvents.dispatchCases[5].2)] := by decide
  rw [rows]
  simp [request, environment, ProofEvents.environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The helper call is admitted from its actual equation arity and strict
source demand, rather than from a native HOL operation. -/
theorem helper_admitted :
    BoundCalls.admitted program "hol-light:axiom" [.var "state", .var "name", .var "term"] = true := by decide

theorem helper_captured (world key label source : Atom) :
    applySubst (capturedEnvironment world key label source) (.var "extension") =
      .symbol "hol-light:axiom" := rfl

theorem arm_enters (world key label source : Atom) (state : State) :
    (BoundCalls.theory program).MultiStep
      { state, control := .evaluate (environment world key label source) arm }
      { state, control := .evaluate (capturedEnvironment world key label source) publicationCall,
        frames := BoundCalls.callerCells 1 } := by
  rw [arm_shape]
  apply BoundCalls.let_enters program (environment world key label source)
    (capturedEnvironment world key label source) state state (.var "extension")
    (.symbol "hol-light:axiom") publicationCall (.symbol "hol-light:axiom")
    (BoundCalls.symbol_returns program _ state "hol-light:axiom")
  simp [capturedEnvironment, environment, ProofEvents.environment,
    SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]

/-- A real call to the quoted dispatcher reaches its publication body with
the AXIOM helper captured. All six pending sequence frames are retained. -/
theorem authored_dispatch_enters_publication (world key label source : Atom)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = world)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label source) :
    (BoundCalls.theory program).MultiStep
      { state, control := .evaluate bindings
          (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) }
      { state, control := .evaluate (capturedEnvironment world key label source) publicationCall,
        frames := BoundCalls.callerCells 6 } := by
  have call := (BoundCalls.CorePath.authored_call_enters program bindings
    (ProofEvents.environment world key (request label source)) state "hol-light:dispatch"
    [stateName,keyName,requestName] ProofEvents.dispatchEquation.body (by rfl) (by decide)
    (by decide) (by decide)
    (by simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, requestCaptured] using
      ProofEvents.dispatch_clause world key (request label source))).extended
  have cases : (BoundCalls.theory program).MultiStep
      { state, control := .evaluate (ProofEvents.environment world key (request label source)) ProofEvents.dispatchEquation.body }
      { state, control := .evaluate (environment world key label source) arm,
        frames := BoundCalls.callerCells 1 } := by
    rw [ProofEvents.dispatch_shape]
    exact BoundCalls.case_enters program (ProofEvents.environment world key (request label source))
      (environment world key label source) state state (.var "request") (request label source) arm
      _ ProofEvents.dispatchCases (Eval.read_cases_encoded ProofEvents.dispatchCases)
      (BoundCalls.variable_returns program _ state "request") (selected world key label source)
  have entered := BoundCalls.path_trans call
    (BoundCalls.path_with_caller_frames program (BoundCalls.callerCells 4) cases)
  have continued := BoundCalls.path_with_caller_frames program (BoundCalls.callerCells 5)
    (arm_enters world key label source state)
  have middle : (BoundCalls.theory program).MultiStep
      { state, control := .evaluate bindings
          (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) }
      { state, control := .evaluate (environment world key label source) arm,
        frames := BoundCalls.callerCells 5 } := by
    simpa [withFrames, BoundCalls.callerCells] using entered
  simpa [withFrames, BoundCalls.callerCells] using BoundCalls.path_trans middle continued

/-- The saved publisher awaits exactly one helper answer, carrying the source
world, event address and full command as already captured argument values. -/
def publicationFrame (world key label source : Atom) : Frame :=
  .argument (capturedEnvironment world key label source) (.function "hol-light:publish")
    [] [world, key, request label source] 3

def helperEntry (world key label source : Atom) (state : State) : Configuration :=
  { state, control := .arguments (capturedEnvironment world key label source)
      (.function "hol-light:axiom") [.var "state", .var "name", .var "term"] [] 0,
    frames := publicationFrame world key label source :: BoundCalls.callerCells 9 }

theorem publication_enters_helper (world key label source : Atom) (state : State) :
    (BoundCalls.theory program).MultiStep
      { state, control := .evaluate (capturedEnvironment world key label source) publicationCall,
        frames := BoundCalls.callerCells 6 }
      (helperEntry world key label source state) := by
  let bound := capturedEnvironment world key label source
  have enter : BoundCalls.CorePath program
      { state, control := .evaluate bound publicationCall }
      { state, control := .arguments bound (.function "hol-light:publish")
          [.var "state", .var "key", .var "request", capturedCall] [] 0 } :=
    .step rfl (DeclarativeSpec.Transition.call_enter rfl (by rfl) (by decide)) (.refl _)
  have arguments := BoundCalls.CorePath.variable_prefix_enters program bound state
    (.function "hol-light:publish") ["state","key","request"] [capturedCall] [] 0
  have capturedArguments : (BoundCalls.theory program).MultiStep
      { state, control := .evaluate bound publicationCall }
      { state, control := .arguments bound (.function "hol-light:publish") [capturedCall]
          [world, key, request label source] 3, frames := BoundCalls.callerCells 3 } := by
    simpa [bound, capturedEnvironment, environment, ProofEvents.environment, applySubst, Subst.lookup]
      using (enter.trans arguments).extended
  have next : (BoundCalls.theory program).MultiStep
      { state, control := .arguments bound (.function "hol-light:publish") [capturedCall]
          [world, key, request label source] 3, frames := BoundCalls.callerCells 3 }
      { state, control := .arguments bound (.function "hol-light:axiom")
          [.var "state", .var "name", .var "term"] [] 0,
        frames := publicationFrame world key label source :: BoundCalls.callerCells 3 } := by
    let waiting : Configuration :=
      { state, control := .evaluate bound capturedCall,
        frames := publicationFrame world key label source :: BoundCalls.callerCells 3 }
    refine .step (u := waiting)
      ?_ (.step (.captured bound "extension" "hol-light:axiom" _ rfl
        (helper_captured world key label source) helper_admitted) (.refl _))
    apply BoundCalls.Transition.core rfl
    apply Eval.step_transition
    have strict : Eval.argumentIsRaw program "hol-light:publish" 3 = false := by decide
    simp [Eval.step, strict, publicationFrame, bound, waiting]
  have composed := BoundCalls.path_trans capturedArguments next
  simpa [withFrames, helperEntry, BoundCalls.callerCells] using
    BoundCalls.path_with_caller_frames program (BoundCalls.callerCells 6) composed

/-- The actual dispatcher reaches its source helper through its captured name.
No term reader, cache hit or axiom-policy assumption is needed for this prefix. -/
theorem authored_dispatch_enters_helper (world key label source : Atom)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = world)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label source) :
    (BoundCalls.theory program).MultiStep
      { state, control := .evaluate bindings
          (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) }
      (helperEntry world key label source state) :=
  BoundCalls.path_trans
    (authored_dispatch_enters_publication world key label source bindings state
      stateName keyName requestName worldCaptured keyCaptured requestCaptured)
    (publication_enters_helper world key label source state)

/-- The source result retains both admission guards and both publication
address guards. A formula dependency is not a cached proof premise. -/
def eventResult (operators constants key label : Atom) (names : Const → Atom)
    (source expected : CheckedSourceTerm) (commitments cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) : Atom :=
  if DBTerm.same source.canonical.term expected.canonical.term then
    if Ty.same source.ty Ty.bool then
      Publication.result operators constants (Lookup.table commitments) key
        (request label (TermReading.sourceAtom source.source)) (.symbol "HOL:Nil")
        (termAtom registeredOperatorAtom names [] source.canonical.term)
        (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
          termAtom registeredOperatorAtom names [] source.canonical.term]]) [] cache receipts
    else .symbol "None"
  else .symbol "None"

/-- Actual AXIOM dispatch executes both readers, the two admission guards and
publication. Formula mismatch and non-Boolean conclusions are refused without
publishing; successful events retain the dependency and command origin. -/
theorem authored_dispatch_classified_return (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (key label : Atom) (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label (TermReading.sourceAtom source.source)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) state
      (eventResult (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        key label constants source expected commitments cache receipts) := by
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let sourceCode := TermReading.sourceAtom source.source
  let sourceWorld := ProofLookup.sourceState operators declarations (Lookup.table commitments) (ReceiptKeys.table receipts) cache
  let before := ProofEvents.environment sourceWorld key (request label sourceCode)
  let selectedBindings := environment sourceWorld key label sourceCode
  let bound := capturedEnvironment sourceWorld key label sourceCode
  let answer := eventResult operators declarations key label constants source expected commitments cache receipts
  have helper : BoundCalls.PureReturns program bound state capturedCall state
      (AxiomExecution.result constants label source expected) := by
    apply BoundCalls.captured_returns_of_literal program bound state state "extension" "hol-light:axiom"
      [.var "state", .var "name", .var "term"] [AxiomExecution.result constants label source expected]
      (helper_captured sourceWorld key label sourceCode) helper_admitted rfl
    exact AxiomExecution.authored_axiom_computed_bound_return world table origins constants identified source expected
      sourceResolved expectedResolved sourceFormed expectedFormed sourceTypeFormed booleanFormed label
      (ReceiptKeys.table receipts) commitments cache found bound state "state" "name" "term" rfl rfl rfl
  have publisher : BoundCalls.PureReturns program bound state publicationCall state answer := by
    cases compared : DBTerm.same source.canonical.term expected.canonical.term with
    | false =>
        have refused : BoundCalls.PureReturns program bound state capturedCall state (.symbol "None") := by
          simpa [AxiomExecution.result, compared] using helper
        simpa [answer, eventResult, compared, publicationCall] using Publication.authored_publish_computed_refused_bound_return
          operators declarations (Lookup.table commitments) key (request label sourceCode) capturedCall cache receipts
          bound state "state" "key" "request" rfl rfl rfl refused
    | true =>
        cases carrier : Ty.same source.ty Ty.bool with
        | false =>
            have refused : BoundCalls.PureReturns program bound state capturedCall state (.symbol "None") := by
              simpa [AxiomExecution.result, compared, carrier] using helper
            simpa [answer, eventResult, compared, carrier, publicationCall] using Publication.authored_publish_computed_refused_bound_return
              operators declarations (Lookup.table commitments) key (request label sourceCode) capturedCall cache receipts
              bound state "state" "key" "request" rfl rfl rfl refused
        | true =>
            have inferred : BoundCalls.PureReturns program bound state capturedCall state
                (.expression [.symbol "Some", Publication.value (.symbol "HOL:Nil")
                  (termAtom registeredOperatorAtom constants [] source.canonical.term)
                  (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
                    termAtom registeredOperatorAtom constants [] source.canonical.term]]) (.symbol "AXIOM")]) := by
              simpa [AxiomExecution.result, compared, carrier] using helper
            simpa [answer, eventResult, compared, carrier, publicationCall] using
              Publication.authored_publish_computed_request_bound_return operators declarations (Lookup.table commitments) key
                (.symbol "HOL:Nil") (termAtom registeredOperatorAtom constants [] source.canonical.term)
                (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
                  termAtom registeredOperatorAtom constants [] source.canonical.term]]) (.symbol "AXIOM")
                (request label sourceCode) []
                (fun captured phase present => Premises.authored_axiom_premises_certificate captured phase label sourceCode "request" present)
                cache receipts bound state "state" "key" "request" capturedCall rfl rfl rfl inferred
  have armReturned : BoundCalls.PureReturns program selectedBindings state arm state answer := by
    rw [arm_shape]
    apply BoundCalls.let_returns program selectedBindings bound state state state (.var "extension")
      (.symbol "hol-light:axiom") publicationCall (.symbol "hol-light:axiom") answer
      (BoundCalls.symbol_returns program selectedBindings state "hol-light:axiom") _ publisher
    simp [bound, selectedBindings, capturedEnvironment, environment, ProofEvents.environment,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:dispatch"
    [stateName,keyName,requestName] ProofEvents.dispatchEquation.body answer
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, requestCaptured] using
      ProofEvents.dispatch_clause sourceWorld key (request label sourceCode)
  · rw [ProofEvents.dispatch_shape]
    exact BoundCalls.case_returns program before selectedBindings state state state (.var "request")
      (request label sourceCode) arm answer _ ProofEvents.dispatchCases (Eval.read_cases_encoded ProofEvents.dispatchCases)
      (BoundCalls.variable_returns program before state "request") (selected sourceWorld key label sourceCode) armReturned

/-- A complete event has the same classified result, including the outer
receipt guard. No inference-result or whole-checker correctness premise is
supplied: the dispatch computation above constructs it. -/
theorem authored_axiom_step_classified_return (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (key label : Atom) (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label (TermReading.sourceAtom source.source)) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
      (eventResult (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
        key label constants source expected commitments cache receipts) := by
  have dispatched := authored_dispatch_classified_return world table origins constants identified source expected
    sourceResolved expectedResolved sourceFormed expectedFormed sourceTypeFormed booleanFormed key label
    commitments cache receipts found
    (ProofEvents.stepEnvironment (OperatorTable.tableAtom table.operators origins)
      (DeclarationTable.tableAtom table constants) (Lookup.table commitments) key
      (request label (TermReading.sourceAtom source.source)) cache receipts)
    state "state" "key" "request" rfl rfl rfl
  have returned := ProofEvents.authored_step_bound_dispatch_return
    (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
    (Lookup.table commitments) key (request label (TermReading.sourceAtom source.source))
    (eventResult (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      key label constants source expected commitments cache receipts)
    cache receipts bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured dispatched
  cases compared : DBTerm.same source.canonical.term expected.canonical.term <;>
    cases carrier : Ty.same source.ty Ty.bool <;>
    cases present : ReceiptKeys.presentB key receipts <;>
    simpa [eventResult, Publication.result, compared, carrier, present] using returned

/-- The full actual event and a registered derivation retain one indexed
formula and one explicit dependency. Authorization is checked against the
selected object theory; no global checker-soundness premise is introduced. -/
theorem authored_axiom_step_derivation (world : TheoryContext) (table : DeclarationTable.Table world)
    (origins : TypeOp → Atom) (constants : Const → Atom) (identified : DeclarationTable.Identifies world constants)
    (source expected : CheckedSourceTerm) (same : source.canonical = expected.canonical)
    (isBool : source.canonical.IsBool)
    (sourceResolved : TermReading.SourceResolved world.signature source.source)
    (expectedResolved : TermReading.SourceResolved world.signature expected.source)
    (sourceFormed : AnnotationsFormed world.signature source.canonical.term)
    (expectedFormed : AnnotationsFormed world.signature expected.canonical.term)
    (sourceTypeFormed : TypeFormed world.signature source.ty) (booleanFormed : TypeFormed world.signature Ty.bool)
    (policy : AxiomPolicy) (key label : Atom)
    (authorized : policy (AxiomExecution.dependency label source isBool).sequent) (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (found : commitments.lookup label = some (TermReading.sourceAtom expected.source))
    (receiptFresh : ReceiptKeys.presentB key receipts = false) (cacheFresh : cache.lookup key = none)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label (TermReading.sourceAtom source.source)) :
    TheoryDerives policy world (AxiomExecution.record label source isBool).fact ∧
      BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
      (.expression [.symbol "Some", Publication.afterState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table constants) (Lookup.table commitments) key
        (request label (TermReading.sourceAtom source.source)) (.symbol "HOL:Nil")
        (termAtom registeredOperatorAtom constants [] source.canonical.term)
        (Premises.keys [.expression [.symbol "HOL:AxiomDependency", label,
          termAtom registeredOperatorAtom constants [] source.canonical.term]]) [] cache receipts]) := by
  refine ⟨AxiomExecution.record_derived policy world label source isBool sourceFormed authorized, ?_⟩
  have returned := authored_axiom_step_classified_return world table origins constants identified source expected
    sourceResolved expectedResolved sourceFormed expectedFormed sourceTypeFormed booleanFormed key label commitments
    cache receipts found bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured

  have termsSame : source.canonical.term = expected.canonical.term := congrArg CanonicalTerm.term same
  have carrier : source.ty = Ty.bool := isBool
  simpa [eventResult, DBTerm.same_eq_true_iff, termsSame, Ty.same_eq_true_iff, carrier,
    Publication.result, receiptFresh, cacheFresh] using returned

/-- Reading a different committed formula cannot create a publication. -/
theorem event_formula_mismatch (operators constants key label : Atom) (names : Const → Atom)
    (source expected : CheckedSourceTerm) (commitments cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (different : source.canonical.term ≠ expected.canonical.term) :
    eventResult operators constants key label names source expected commitments cache receipts = .symbol "None" := by
  simp [eventResult, DBTerm.same_eq_true_iff, different]

/-- An equal but non-Boolean source is still refused by the profile's
conclusion gate. Merely reading a well-formed term does not admit an axiom. -/
theorem event_non_boolean (operators constants key label : Atom) (names : Const → Atom)
    (source expected : CheckedSourceTerm) (commitments cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (notBool : source.ty ≠ Ty.bool) :
    eventResult operators constants key label names source expected commitments cache receipts = .symbol "None" := by
  cases compared : DBTerm.same source.canonical.term expected.canonical.term <;>
    simp [eventResult, compared, Ty.same_eq_true_iff, notBool]

/-- An absent label refuses the actual captured helper, nested publication and
dispatcher for arbitrary source payloads and finite retained address tables. -/
theorem authored_dispatch_missing_return (operators constants key label source : Atom)
    (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (missing : commitments.lookup label = none)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label source) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName])
      state (.symbol "None") := by
  let world := ProofLookup.sourceState operators constants (Lookup.table commitments) (ReceiptKeys.table receipts) cache
  let before := ProofEvents.environment world key (request label source)
  let selectedBindings := environment world key label source
  let bound := capturedEnvironment world key label source
  have helper : BoundCalls.PureReturns program bound state capturedCall state (.symbol "None") := by
    apply BoundCalls.captured_returns_of_literal program bound state state "extension" "hol-light:axiom"
      [.var "state", .var "name", .var "term"] [.symbol "None"] (helper_captured world key label source)
      helper_admitted rfl
    exact AxiomExecution.authored_axiom_missing_bound_return operators constants label source (ReceiptKeys.table receipts)
      commitments cache missing bound state "state" "name" "term" rfl rfl rfl
  have publisher : BoundCalls.PureReturns program bound state publicationCall state (.symbol "None") :=
    Publication.authored_publish_computed_refused_bound_return operators constants (Lookup.table commitments)
      key (request label source) capturedCall cache receipts bound state "state" "key" "request" rfl rfl rfl helper
  have armReturned : BoundCalls.PureReturns program selectedBindings state arm state (.symbol "None") := by
    rw [arm_shape]
    apply BoundCalls.let_returns program selectedBindings bound state state state (.var "extension")
      (.symbol "hol-light:axiom") publicationCall (.symbol "hol-light:axiom") (.symbol "None")
      (BoundCalls.symbol_returns program selectedBindings state "hol-light:axiom") _ publisher
    simp [bound, selectedBindings, capturedEnvironment, environment, ProofEvents.environment,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:dispatch"
    [stateName,keyName,requestName] ProofEvents.dispatchEquation.body (.symbol "None")
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, requestCaptured] using
      ProofEvents.dispatch_clause world key (request label source)
  · rw [ProofEvents.dispatch_shape]
    exact BoundCalls.case_returns program before selectedBindings state state state (.var "request")
      (request label source) arm (.symbol "None") _ ProofEvents.dispatchCases
      (Eval.read_cases_encoded ProofEvents.dispatchCases)
      (BoundCalls.variable_returns program before state "request") (selected world key label source) armReturned

/-- The complete quoted event refuses every undeclared AXIOM label. This
includes the outer receipt guard and actual captured-call dispatcher. The
requested source formula remains arbitrary and the entire store is retained. -/
theorem authored_missing_axiom_step_refused (operators constants key label source : Atom)
    (commitments cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (missing : commitments.lookup label = none)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) = ProofLookup.sourceState
      operators constants (Lookup.table commitments) (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request label source) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName])
      state (.symbol "None") := by
  have dispatched := authored_dispatch_missing_return operators constants key label source commitments cache receipts missing
    (ProofEvents.stepEnvironment operators constants (Lookup.table commitments) key (request label source) cache receipts)
    state "state" "key" "request" rfl rfl rfl
  have returned := ProofEvents.authored_step_bound_dispatch_return operators constants (Lookup.table commitments)
    key (request label source) (.symbol "None") cache receipts bindings state stateName keyName requestName
    worldCaptured keyCaptured requestCaptured dispatched
  simpa using returned

end Mettapedia.Languages.HOLLight.MeTTa.AxiomDispatch
