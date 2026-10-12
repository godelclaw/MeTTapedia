import Mettapedia.Languages.HOLLight.MeTTa.Publication
import Mettapedia.Languages.HOLLight.MeTTa.InferenceExecution

/-!
# Actual inference events through the authored HOL dispatcher

The event guard, inference dispatcher and theorem publisher execute the quoted
source. A repeated receipt address is refused before dispatch. Successful
inference results retain their exact cache payload and ordered premise receipt.
Source rule preservation does not yet authorize every definition/cache history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.ProofEvents

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation
open Eval
open Effects (State boolean)

def dispatchEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:dispatch"))[0]'(by decide)
def dispatchCases : SpaceSemantics.Cases :=
  match dispatchEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def selected : Atom := .expression [.symbol "hol-light:publish", .var "state", .var "key", .var "request",
  .expression [.symbol "hol-light:infer", .var "state", .var "request"]]
def environment (source key request : Atom) : Subst := [("request", request), ("key", key), ("state", source)]

/-- The actual dispatcher binds its ordinary inference arm in this environment.
It retains the original source state, event key and complete command. -/
def inferenceEnvironment (operators constants axioms key : Atom) (kind : InferenceKind) (payload first second : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  ("inference", Premises.request kind payload first second) ::
    environment (ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
      key (Premises.request kind payload first second)

theorem dispatch_shape : dispatchEquation.body = .expression [.symbol "case", .var "request",
    .expression (dispatchCases.map fun row => .expression [row.1,row.2])] := by decide
theorem dispatch_clause (source key request : Atom) :
    clauses program "hol-light:dispatch" [source,key,request] = [.evaluate (environment source key request) dispatchEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:dispatch") = [dispatchEquation] := rfl
  rw [unique]
  have formals : dispatchEquation.arguments = [.var "state", .var "key", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
private theorem dispatch_selection (operators constants axioms key : Atom) (kind : InferenceKind) (payload first second : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    SpaceSemantics.selectCase
      (environment (ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
        key (Premises.request kind payload first second)) (Premises.request kind payload first second) dispatchCases =
      some (inferenceEnvironment operators constants axioms key kind payload first second cache receipts, selected) := by
  have patterns : dispatchCases = [
      (.expression [.symbol "DECLARE_TYPE", .var "name", .var "arity"], (dispatchCases[0]'(by decide)).2),
      (.expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], (dispatchCases[1]'(by decide)).2),
      (.expression [.symbol "DEFINITION", .var "name", .var "schema", .var "body"], (dispatchCases[2]'(by decide)).2),
      (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], (dispatchCases[3]'(by decide)).2),
      (.expression [.symbol "AXIOM", .var "name", .var "term"], (dispatchCases[4]'(by decide)).2),
      (.var "inference", selected)] := by decide
  rw [patterns]
  cases kind <;> simp [Premises.request, environment, inferenceEnvironment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Execute the actual dispatcher after an actual inference returns its
theorem payload. All ten primitive request forms use this same publisher. -/
theorem authored_dispatch_inference_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (inferred : PureReturns program (inferenceEnvironment operators constants axioms key kind payload first second cache receipts) state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value hypotheses conclusion dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:dispatch", .var stateKey, .var keyName, .var requestName]) state
      (Publication.result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts) := by
  let source := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let request := Premises.request kind payload first second
  let before := environment source key request
  let bound := inferenceEnvironment operators constants axioms key kind payload first second cache receipts
  apply authored_variable_call_returns program bindings before state state "hol-light:dispatch" [stateKey,keyName,requestName]
    dispatchEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured] using dispatch_clause source key request
  · rw [dispatch_shape]
    apply case_returns program before bound state state state (.var "request") request selected _ _ dispatchCases
      (read_cases_encoded dispatchCases)
    · exact variable_returns program before state "request"
    · exact dispatch_selection operators constants axioms key kind payload first second cache receipts
    · exact Publication.authored_publish_inference_return operators constants axioms key hypotheses conclusion dependencies origin
        kind payload first second cache receipts bound state "state" "key" "request"
        (by simp [bound, inferenceEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, inferenceEnvironment, environment, applySubst, Subst.lookup])
        (by simp [bound, inferenceEnvironment, environment, applySubst, Subst.lookup]) inferred

private def stepEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:step"))[0]'(by decide)
private def guardBody : Atom := .expression [.symbol "if",
  .expression [.symbol "hol-light:receipt-key-present", .var "key", .var "receipts"], .symbol "None",
  .expression [.symbol "hol-light:dispatch", .var "state", .var "key", .var "request"]]
private def stepCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms", .var "cache", .var "receipts"], guardBody),
    (.var "malformed", .symbol "None")]
def stepEnvironment (operators constants axioms key request : Atom) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) : Subst :=
  [("receipts", ReceiptKeys.table receipts), ("cache", Lookup.table cache), ("axioms", axioms),
    ("constants", constants), ("operators", operators)] ++
    environment (ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache) key request
private theorem step_shape : stepEquation.body = .expression [.symbol "case", .var "state",
    .expression (stepCases.map fun row => .expression [row.1,row.2])] := by decide
private theorem step_clause (source key request : Atom) :
    clauses program "hol-light:step" [source,key,request] = [.evaluate (environment source key request) stepEquation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:step") = [stepEquation] := rfl
  rw [unique]
  have formals : stepEquation.arguments = [.var "state", .var "key", .var "request"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The complete actual event adds its fresh checked result, or refuses an
occupied address. Logical correctness is earned by the particular inference
execution supplied here, rather than by publication. -/
theorem authored_step_dispatch_return (operators constants axioms key request computed : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (dispatched : PureReturns program (stepEnvironment operators constants axioms key request cache receipts) state
      (.expression [.symbol "hol-light:dispatch", .var "state", .var "key", .var "request"]) state computed) :
    PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
      (if ReceiptKeys.presentB key receipts then .symbol "None" else computed) := by
  let source := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let before := environment source key request
  let bound := stepEnvironment operators constants axioms key request cache receipts
  apply authored_variable_call_returns program bindings before state state "hol-light:step" [stateKey,keyName,requestName]
    stepEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured] using step_clause source key request
  · rw [step_shape]
    apply case_returns program before bound state state state (.var "state") source guardBody _ _ stepCases
      (read_cases_encoded stepCases)
    · exact variable_returns program before state "state"
    · simp [stepCases, stepEnvironment, bound, before, environment, source, ProofLookup.sourceState,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold guardBody
      apply if_returns program bound state state state _ (boolean (ReceiptKeys.presentB key receipts)) _ _ _
      · exact ReceiptKeys.authored_receipt_key_present_return bound state key receipts "key" "receipts"
          (by simp [bound, stepEnvironment, environment, applySubst, Subst.lookup])
          (by simp [bound, stepEnvironment, applySubst, Subst.lookup])
      · cases present : ReceiptKeys.presentB key receipts with
        | false =>
            simp only [boolean]
            exact dispatched
        | true => simpa only [present, ↓reduceIte, boolean, BEq.rfl] using symbol_returns program bound state "None"

/-- Captured-call dispatch uses the same quoted outer guard and constructed
receipt certificate. Its continuation may execute a captured helper. -/
theorem authored_step_bound_dispatch_return (operators constants axioms key request computed : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (dispatched : BoundCalls.PureReturns program (stepEnvironment operators constants axioms key request cache receipts) state
      (.expression [.symbol "hol-light:dispatch", .var "state", .var "key", .var "request"]) state computed) :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
      (if ReceiptKeys.presentB key receipts then .symbol "None" else computed) := by
  let source := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let before := environment source key request
  let bound := stepEnvironment operators constants axioms key request cache receipts
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:step" [stateKey,keyName,requestName]
    stepEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured] using step_clause source key request
  · rw [step_shape]
    apply BoundCalls.case_returns program before bound state state state (.var "state") source guardBody _ _ stepCases
      (read_cases_encoded stepCases)
    · exact BoundCalls.variable_returns program before state "state"
    · simp [stepCases, stepEnvironment, bound, before, environment, source, ProofLookup.sourceState,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold guardBody
      apply BoundCalls.if_returns program bound state state state _ (boolean (ReceiptKeys.presentB key receipts)) _ _ _
      · exact ReceiptKeys.authored_receipt_key_present_bound_return bound state key receipts "key" "receipts"
          (by simp [bound, stepEnvironment, environment, applySubst, Subst.lookup])
          (by simp [bound, stepEnvironment, applySubst, Subst.lookup])
      · cases present : ReceiptKeys.presentB key receipts with
        | false =>
            simp only [boolean]
            exact dispatched
        | true => simpa only [present, ↓reduceIte, boolean, BEq.rfl] using BoundCalls.symbol_returns program bound state "None"

/-- Primitive inference events instantiate the general guarded dispatcher law. -/
theorem authored_step_inference_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (inferred : PureReturns program (inferenceEnvironment operators constants axioms key kind payload first second cache receipts) state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state
      (.expression [.symbol "Some", Publication.value hypotheses conclusion dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
      (Publication.result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts) := by
  have dispatched := authored_dispatch_inference_return operators constants axioms key hypotheses conclusion dependencies origin
    kind payload first second cache receipts
    (stepEnvironment operators constants axioms key (Premises.request kind payload first second) cache receipts) state
    "state" "key" "request" rfl rfl rfl inferred
  have returned := authored_step_dispatch_return operators constants axioms key (Premises.request kind payload first second)
    (Publication.result operators constants axioms key (Premises.request kind payload first second)
      hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts)
    cache receipts bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured dispatched
  cases present : ReceiptKeys.presentB key receipts
  · simpa only [present, Bool.false_eq_true, ↓reduceIte] using returned
  · simpa only [Publication.result, present, ↓reduceIte] using returned

/-- Reusing a receipt key is refused before dispatch for any captured command.
No inference-execution premise is needed, and the store remains unchanged. -/
theorem authored_step_duplicate_refused (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (occupied : ReceiptKeys.presentB key receipts = true)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request) :
    PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName])
      state (.symbol "None") := by
  let source := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let before := environment source key request
  let bound := stepEnvironment operators constants axioms key request cache receipts
  apply authored_variable_call_returns program bindings before state state "hol-light:step" [stateKey,keyName,requestName]
    stepEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured] using step_clause source key request
  · rw [step_shape]
    apply case_returns program before bound state state state (.var "state") source guardBody _ _ stepCases
      (read_cases_encoded stepCases)
    · exact variable_returns program before state "state"
    · simp [stepCases, stepEnvironment, bound, before, environment, source, ProofLookup.sourceState,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold guardBody
      apply if_returns program bound state state state _ (boolean true) _ _ _
      · simpa only [occupied] using ReceiptKeys.authored_receipt_key_present_return bound state key receipts "key" "receipts"
          (by simp [bound, stepEnvironment, environment, applySubst, Subst.lookup])
          (by simp [bound, stepEnvironment, applySubst, Subst.lookup])
      · simpa only [boolean, BEq.rfl, ↓reduceIte] using symbol_returns program bound state "None"

/-- A complete actual REFL event reads its source, constructs the shared rule
derivation and publishes precisely that theorem with its command receipt.
Freshness determines whether publication succeeds; it does not change REFL's
logical validity. Old cache authorization remains a separate invariant. -/
theorem authored_refl_step_derivation (world : DefinitionAdapters.TheoryContext)
    (table : DeclarationTable.Table world) (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (source : CheckedSourceTerm) (resolved : TermReading.SourceResolved world.signature source.source)
    (annotations : AnnotationsFormed world.signature source.canonical.term)
    (key axioms : Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) =
      .expression [.symbol "REFL", TermReading.sourceAtom source.source]) (policy : AxiomPolicy) :
    ∃ out : Theorem, InferenceRequest.Semantics (.refl source.canonical) out ∧
      Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out ∧ out.axioms = ∅ ∧ out.sequent.hyp = ∅ ∧
      PureReturns program bindings state (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (Publication.result (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants) axioms key
          (.expression [.symbol "REFL", TermReading.sourceAtom source.source]) (.symbol "HOL:Nil")
          (Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term)
          (.symbol "HOL:Nil") [] cache receipts) := by
  let operators := OperatorTable.tableAtom table.operators origins
  let declarations := DeclarationTable.tableAtom table constants
  let bound := inferenceEnvironment operators declarations axioms key .refl (TermReading.sourceAtom source.source)
    (.symbol "None") (.symbol "None") cache receipts
  obtain ⟨out, semantics, derived, dependencies, hypotheses, returned⟩ :=
    InferenceExecution.authored_refl_derivation world table origins constants equalityIdentity source resolved annotations
      bound state axioms (ReceiptKeys.table receipts) cache "state" "request"
      (by simp [bound, inferenceEnvironment, environment, operators, declarations, applySubst, Subst.lookup])
      (by simp [bound, inferenceEnvironment, environment, Premises.request, applySubst, Subst.lookup]) policy
  refine ⟨out, semantics, derived, dependencies, hypotheses, ?_⟩
  exact authored_step_inference_return operators declarations axioms key (.symbol "HOL:Nil")
    (Representation.termAtom Representation.registeredOperatorAtom constants [] out.sequent.concl.term)
    (.symbol "HOL:Nil") (.symbol "REFL") .refl (TermReading.sourceAtom source.source) (.symbol "None") (.symbol "None")
    cache receipts bindings state stateKey keyName requestName stateCaptured keyCaptured requestCaptured returned

end Mettapedia.Languages.HOLLight.MeTTa.ProofEvents
