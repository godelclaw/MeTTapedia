import Mettapedia.Languages.HOLLight.MeTTa.DeclarationExecution

/-!
# Complete constant declaration events and retained derivation histories

The real event dispatcher captures the authored declaration helper. Its
execution keeps the outer receipt guard, the source name/schema guards and
the exact registered context extension together. A successful event preserves
the logical evidence of every old cache entry and their source representation.
The source store is unchanged: the returned theory state is an immutable value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DeclarationEvents

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Eval (read_cases_encoded)
open Effects (State)
open DeclarationExecution

private def constantArm : Atom := ProofEvents.dispatchCases[1].2
private def capturedCall : Atom :=
  .expression [.var "extension", .var "state", .var "key", .var "name", .var "schema"]
private def environment (world key : Atom) (name : String) (schema : Ty) : Subst :=
  [("schema", TypeSubstitution.typeAtom Representation.registeredOperatorAtom schema),
    ("name", .grounded (.string name))] ++
    ProofEvents.environment world key (constantRequest name schema)
private def capturedEnvironment (world key : Atom) (name : String) (schema : Ty) : Subst :=
  ("extension", .symbol "hol-light:declare-constant") :: environment world key name schema

private theorem arm_shape : constantArm =
    .expression [.symbol "let", .var "extension", .symbol "hol-light:declare-constant", capturedCall] := by decide

private theorem selected (world key : Atom) (name : String) (schema : Ty) :
    SpaceSemantics.selectCase
      (ProofEvents.environment world key (constantRequest name schema))
      (constantRequest name schema) ProofEvents.dispatchCases =
      some (environment world key name schema, constantArm) := by
  have rows : ProofEvents.dispatchCases =
      [(.expression [.symbol "DECLARE_TYPE", .var "name", .var "arity"], ProofEvents.dispatchCases[0].2),
       (.expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], constantArm),
       (.expression [.symbol "DEFINITION", .var "name", .var "schema", .var "body"], ProofEvents.dispatchCases[2].2),
       (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], ProofEvents.dispatchCases[3].2),
       (.expression [.symbol "AXIOM", .var "name", .var "term"], ProofEvents.dispatchCases[4].2),
       (.var "inference", ProofEvents.dispatchCases[5].2)] := by decide
  rw [rows]
  simp [constantRequest, environment, ProofEvents.environment, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The real captured helper computes the complete declaration result. No
native declaration primitive replaces its name, formation or lookup checks. -/
theorem authored_constant_dispatch (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved context.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = constantRequest name schema) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:dispatch", .var stateName, .var keyName, .var requestName]) state
      (constantResult context table origins identity axioms key name schema cache receipts) := by
  let world := ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
    (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache
  let before := ProofEvents.environment world key (constantRequest name schema)
  let chosen := environment world key name schema
  let captured := capturedEnvironment world key name schema
  have helper : BoundCalls.PureReturns program captured state capturedCall state
      (constantResult context table origins identity axioms key name schema cache receipts) := by
    apply BoundCalls.captured_returns_of_literal program captured state state
      "extension" "hol-light:declare-constant" [.var "state", .var "key", .var "name", .var "schema"]
      [constantResult context table origins identity axioms key name schema cache receipts] rfl
      (by decide) rfl
    exact (authored_constant_certificate context table origins identity axioms key name schema resolved
      cache receipts captured state "state" "key" "name" "schema" rfl rfl rfl rfl).extended
  have armReturned : BoundCalls.PureReturns program chosen state constantArm state
      (constantResult context table origins identity axioms key name schema cache receipts) := by
    rw [arm_shape]
    apply BoundCalls.let_returns program chosen captured state state state (.var "extension")
      (.symbol "hol-light:declare-constant") capturedCall (.symbol "hol-light:declare-constant") _
      (BoundCalls.symbol_returns program chosen state "hol-light:declare-constant") _ helper
    simp [captured, chosen, capturedEnvironment, environment, ProofEvents.environment,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  apply BoundCalls.authored_variable_call_returns program bindings before state state "hol-light:dispatch"
    [stateName, keyName, requestName] ProofEvents.dispatchEquation.body _
    (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, worldCaptured, keyCaptured, requestCaptured] using
      ProofEvents.dispatch_clause world key (constantRequest name schema)
  · rw [ProofEvents.dispatch_shape]
    exact BoundCalls.case_returns program before chosen state state state (.var "request")
      (constantRequest name schema) constantArm _ _ ProofEvents.dispatchCases
      (read_cases_encoded ProofEvents.dispatchCases)
      (BoundCalls.variable_returns program before state "request") (selected world key name schema) armReturned

/-- The outer source event refuses an occupied receipt address before
dispatch. Otherwise its captured helper performs the actual declaration. -/
theorem authored_constant_step (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (identity : Const → Atom)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved context.signature schema)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = constantRequest name schema) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
      (if ReceiptKeys.presentB key receipts then .symbol "None" else
        constantResult context table origins identity axioms key name schema cache receipts) := by
  have dispatched := authored_constant_dispatch context table origins identity axioms key name schema resolved
    cache receipts
    (ProofEvents.stepEnvironment (OperatorTable.tableAtom table.operators origins)
      (DeclarationTable.tableAtom table identity) axioms key (constantRequest name schema) cache receipts)
    state "state" "key" "request" rfl rfl rfl
  exact ProofEvents.authored_step_bound_dispatch_return
    (OperatorTable.tableAtom table.operators origins) (DeclarationTable.tableAtom table identity)
    axioms key (constantRequest name schema)
    (constantResult context table origins identity axioms key name schema cache receipts)
    cache receipts bindings state stateName keyName requestName worldCaptured keyCaptured requestCaptured dispatched

/-- A successful complete event constructs the registered extension and
transports every old authorized derivation without changing its source data.
The resulting identity map also identifies the new declaration faithfully. -/
theorem authored_constant_step_preserves_history (policy : AxiomPolicy) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (identity : Const → Atom)
    (identified : DeclarationTable.Identifies context identity)
    (axioms key : Atom) (name : String) (schema : Ty)
    (resolved : TypeFormation.Resolved context.signature schema)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (Name.global name) ∉ context.names)
    (cache : CacheAuthorization.Cache) (valid : CacheAuthorization.Valid policy context cache)
    (receipts : List ReceiptKeys.Entry) (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (bindings : Subst) (state : State) (stateName keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateName) =
      ProofLookup.sourceState (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms (ReceiptKeys.table receipts)
        (CacheAuthorization.entries identity cache))
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = constantRequest name schema) :
    let extended := context.addConstant (constant name) schema formed fresh
    let identities := DeclarationTable.extendIdentity identity (constant name) (constantIdentity name)
    let declarations := DeclarationTable.addConstant table (constant name) schema formed fresh
    DeclarationTable.Identifies extended identities ∧
      CacheAuthorization.Valid policy extended cache ∧
      CacheAuthorization.entries identities cache = CacheAuthorization.entries identity cache ∧
      BoundCalls.PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateName, .var keyName, .var requestName]) state
        (.expression [.symbol "Some", ProofLookup.sourceState
          (OperatorTable.tableAtom declarations.operators origins)
          (DeclarationTable.tableAtom declarations identities) axioms
          (ReceiptKeys.table (⟨key, constantRequest name schema, []⟩ :: receipts))
          (CacheAuthorization.entries identities cache)]) := by
  dsimp only
  have retained := constant_preserves_authorized_cache policy context identity name schema formed fresh cache valid
  refine ⟨DeclarationTable.extended_identity_identifies context identity identified (constant name) schema
      formed fresh (constantIdentity name) rfl, retained.1, retained.2, ?_⟩
  have returned := authored_constant_step context table origins identity axioms key name schema resolved
    (CacheAuthorization.entries identity cache) receipts bindings state stateName keyName requestName
    worldCaptured keyCaptured requestCaptured
  have absent := DeclarationTable.fresh_name_absent table identity (Name.global name) fresh
  have absentSource : (DeclarationTable.entriesAtom table identity).lookup (.grounded (.string name)) = none := by
    exact absent
  have accepted : constantResult context table origins identity axioms key name schema
      (CacheAuthorization.entries identity cache) receipts =
      .expression [.symbol "Some", constantAfter (OperatorTable.tableAtom table.operators origins)
        (DeclarationTable.tableAtom table identity) axioms key name schema
        (CacheAuthorization.entries identity cache) receipts] := by
    simp [constantResult, (typeFormedB_eq_true_iff _ _).mpr formed, absentSource]
  rw [receiptFresh, accepted] at returned
  simp only [Bool.false_eq_true, ↓reduceIte] at returned
  rw [constant_after_registered context table origins identity axioms key name schema formed fresh,
    ← retained.2] at returned
  exact returned

end Mettapedia.Languages.HOLLight.MeTTa.DeclarationEvents
