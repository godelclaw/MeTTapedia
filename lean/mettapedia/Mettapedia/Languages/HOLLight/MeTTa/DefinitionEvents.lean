import Mettapedia.Languages.HOLLight.MeTTa.DefinitionExecution

/-!
# Complete authored constant-definition events

The retained dispatcher captures its definition helper. The outer receipt
guard and actual definition classification compose in the same source
machine, including refusal of open bodies and hidden type parameters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DefinitionEvents

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval (read_cases_encoded)
open Effects (State)
open DefinitionExecution

private def definitionArm : Atom := ProofEvents.dispatchCases[2].2
private def capturedCall : Atom :=
  .expression [.var "extension", .var "state", .var "key", .var "name", .var "schema", .var "body"]
private def environment (world key : Atom) (name : String) (body : CheckedSourceTerm) : Subst :=
  [("body", TermReading.sourceAtom body.source),
   ("schema", TypeSubstitution.typeAtom Representation.registeredOperatorAtom body.ty),
   ("name", .grounded (.string name))] ++ ProofEvents.environment world key (definitionRequest name body)
private def capturedEnvironment (world key : Atom) (name : String) (body : CheckedSourceTerm) : Subst :=
  ("extension", .symbol "hol-light:definition") :: environment world key name body

private theorem arm_shape : definitionArm =
    .expression [.symbol "let", .var "extension", .symbol "hol-light:definition", capturedCall] := by decide
private theorem selected (world key : Atom) (name : String) (body : CheckedSourceTerm) :
    SpaceSemantics.selectCase (ProofEvents.environment world key (definitionRequest name body))
      (definitionRequest name body) ProofEvents.dispatchCases =
      some (environment world key name body, definitionArm) := by
  have rows : ProofEvents.dispatchCases =
      [(.expression [.symbol "DECLARE_TYPE", .var "name", .var "arity"], ProofEvents.dispatchCases[0].2),
       (.expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], ProofEvents.dispatchCases[1].2),
       (.expression [.symbol "DEFINITION", .var "name", .var "schema", .var "body"], definitionArm),
       (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], ProofEvents.dispatchCases[3].2),
       (.expression [.symbol "AXIOM", .var "name", .var "term"], ProofEvents.dispatchCases[4].2),
       (.var "inference", ProofEvents.dispatchCases[5].2)] := by decide
  rw [rows]
  simp [definitionRequest, environment, ProofEvents.environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The actual captured helper classifies every resolved, formed checked
body at a fresh global definition name, including both definition refusals. -/
theorem authored_definition_dispatch (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = definitionRequest name body) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:dispatch", .var stateKey, .var keyName, .var requestName]) state
      (classifiedResult context table origins constants axioms key name body cache receipts) := by
  let world := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table constants) axioms (ReceiptKeys.table receipts) cache
  let before := ProofEvents.environment world key (definitionRequest name body)
  let chosen := environment world key name body
  let captured := capturedEnvironment world key name body
  have helper : BoundCalls.PureReturns program captured state capturedCall state
      (classifiedResult context table origins constants axioms key name body cache receipts) := by
    apply BoundCalls.captured_returns_of_literal program captured state state
      "extension" "hol-light:definition" [.var "state", .var "key", .var "name", .var "schema", .var "body"]
      [classifiedResult context table origins constants axioms key name body cache receipts] rfl (by decide) rfl
    exact authored_definition_classified_return context table origins constants equalityIdentity axioms key name body
      sourceResolved schemaResolved formed schemaFormed fresh cache receipts captured state "state" "key" "name" "schema" "body"
      rfl rfl rfl rfl rfl
  have armReturned : BoundCalls.PureReturns program chosen state definitionArm state
      (classifiedResult context table origins constants axioms key name body cache receipts) := by
    rw [arm_shape]
    apply BoundCalls.let_returns program chosen captured state state state (.var "extension")
      (.symbol "hol-light:definition") capturedCall (.symbol "hol-light:definition") _
      (BoundCalls.symbol_returns program chosen state "hol-light:definition") _ helper
    simp [captured, chosen, capturedEnvironment, environment, ProofEvents.environment,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:dispatch"
    [stateKey, keyName, requestName] ProofEvents.dispatchEquation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, requestCaptured] using
      ProofEvents.dispatch_clause world key (definitionRequest name body)
  · rw [ProofEvents.dispatch_shape]
    exact BoundCalls.case_returns program before chosen state state state (.var "request")
      (definitionRequest name body) definitionArm _ _ ProofEvents.dispatchCases
      (read_cases_encoded ProofEvents.dispatchCases)
      (BoundCalls.variable_returns program before state "request") (selected world key name body) armReturned

/-- The complete source event retains the first receipt check and the
publisher's cache/receipt checks, with no uncommitted theory update escaping. -/
theorem authored_definition_step (context : TheoryContext) (table : DeclarationTable.Table context)
    (origins : TypeOp → Atom) (constants : Const → Atom)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (axioms key : Atom) (name : String) (body : CheckedSourceTerm)
    (sourceResolved : TermReading.SourceResolved context.signature body.source)
    (schemaResolved : TypeFormation.Resolved context.signature body.ty)
    (formed : AnnotationsFormed context.signature body.canonical.term)
    (schemaFormed : TypeFormed context.signature body.ty)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
      axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = definitionRequest name body) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
      (if ReceiptKeys.presentB key receipts then .symbol "None" else
        classifiedResult context table origins constants axioms key name body cache receipts) := by
  have dispatched := authored_definition_dispatch context table origins constants equalityIdentity axioms key name body
    sourceResolved schemaResolved formed schemaFormed fresh cache receipts
    (ProofEvents.stepEnvironment (OperatorTable.tableAtom table.operators origins)
      (DeclarationTable.tableAtom table constants) axioms key (definitionRequest name body) cache receipts)
    state "state" "key" "request" rfl rfl rfl
  exact ProofEvents.authored_step_bound_dispatch_return
    (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table constants)
    axioms key (definitionRequest name body) (classifiedResult context table origins constants axioms key name body cache receipts)
    cache receipts bindings state stateKey keyName requestName worldCaptured keyCaptured requestCaptured dispatched

end Mettapedia.Languages.HOLLight.MeTTa.DefinitionEvents
