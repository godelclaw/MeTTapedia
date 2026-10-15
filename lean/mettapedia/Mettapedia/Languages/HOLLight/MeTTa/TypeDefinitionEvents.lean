import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionExecution

/-!
# Complete authored type-definition events

The dispatcher captures the actual command helper. The outer receipt guard,
the command's name and premise guards, and both inner publications execute
in the same source machine. This path does not itself authorize an initial
proof cache or identify native dependent equality with HOL equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEvents

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters
open Effects (State)
open TypeDefinitionConstruction (Input)
open TypeDefinitionExecution (world)

def command (input : Input) : Atom := TypeDefinitionFormation.command
  input.typeName input.abstractionName input.representationName input.premise

private def arm : Atom := ProofEvents.dispatchCases[3].2
private def callNames : List String := ["state", "key", "name", "abs", "rep", "premise"]
private def capturedCall : Atom := .expression (.var "extension" :: callNames.map Atom.var)
private def environment (input : Input) : Subst :=
  [("premise", input.premise), ("rep", .grounded (.string input.representationName)),
   ("abs", .grounded (.string input.abstractionName)), ("name", .grounded (.string input.typeName))] ++
    ProofEvents.environment (world input) input.key (command input)

private theorem arm_shape : arm =
    .expression [.symbol "let", .var "extension", .symbol "hol-light:type-definition", capturedCall] := by decide

private theorem selected (input : Input) :
    SpaceSemantics.selectCase (ProofEvents.environment (world input) input.key (command input))
      (command input) ProofEvents.dispatchCases = some (environment input, arm) := by
  have rows : ProofEvents.dispatchCases =
      [(.expression [.symbol "DECLARE_TYPE", .var "name", .var "arity"], ProofEvents.dispatchCases[0].2),
       (.expression [.symbol "DECLARE_CONSTANT", .var "name", .var "schema"], ProofEvents.dispatchCases[1].2),
       (.expression [.symbol "DEFINITION", .var "name", .var "schema", .var "body"], ProofEvents.dispatchCases[2].2),
       (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], arm),
       (.expression [.symbol "AXIOM", .var "name", .var "term"], ProofEvents.dispatchCases[4].2),
       (.var "inference", ProofEvents.dispatchCases[5].2)] := by decide
  rw [rows]
  simp [command, TypeDefinitionFormation.command, environment, ProofEvents.environment,
    SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- A fresh event address enters the captured command and reaches its two
publications. Declaration and proof side conditions are those executed by
the retained command; the actual proof cache remains its only premise input. -/
theorem authored_step_returns (input : Input) (context : TheoryContext)
    (table : DeclarationTable.Table context) (origins : TypeOp → Atom) (constants : Const → Atom)
    (operatorTable : input.operators = OperatorTable.tableAtom table.operators origins)
    (constantTable : input.declarations = DeclarationTable.tableAtom table constants)
    (predicate : CheckedSourceTerm) (witness : CanonicalTerm) (origin : Atom)
    (found : input.cache.lookup input.premise =
      some (TypeDefinitionExecution.premiseValue input constants predicate witness origin))
    (typeFresh : .typeOperator (sourceOperatorName (Name.global input.typeName)) ∉ context.names)
    (absFresh : .constant (Name.global input.abstractionName) ∉ context.names)
    (repFresh : .constant (Name.global input.representationName) ∉ context.names)
    (different : input.abstractionName ≠ input.representationName)
    (global : TypeParameterOrdering.globalParameters predicate.canonical.term)
    (typed : predicate.ty = .function witness.ty Ty.bool)
    (formed : AnnotationsFormed context.signature predicate.canonical.term)
    (closed : predicate.canonical.term.HasNoFreeVariables)
    (equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality)
    (receiptFresh : ReceiptKeys.presentB input.key input.receipts = false)
    (cacheFresh : input.cache.lookup input.key = none)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (worldCaptured : applySubst bindings (.var stateKey) = world input)
    (keyCaptured : applySubst bindings (.var keyName) = input.key)
    (requestCaptured : applySubst bindings (.var requestName) = command input) :
    ∃ texts, texts.map Name.global = sortedParameters predicate.source ∧
      BoundCalls.PureReturns program bindings state
        (.expression [.symbol "hol-light:step", .var stateKey, .var keyName, .var requestName]) state
        (TypeDefinitionConstruction.result input constants predicate witness.ty texts) := by
  let chosen := environment input
  let captured := ("extension", .symbol "hol-light:type-definition") :: chosen
  obtain ⟨texts, ordered, returned⟩ := TypeDefinitionExecution.authored_command_returns input context table origins constants
    operatorTable constantTable predicate witness origin found typeFresh absFresh repFresh different global typed formed closed
    equalityIdentity receiptFresh cacheFresh captured state callNames (by
      simp [captured, chosen, environment, callNames, ProofEvents.environment,
        TypeDefinitionExecution.sourceArguments, applySubst, Subst.lookup])
  have capturedReturned : BoundCalls.PureReturns program captured state capturedCall state
      (TypeDefinitionConstruction.result input constants predicate witness.ty texts) :=
    BoundCalls.captured_returns_of_literal program captured state state "extension" "hol-light:type-definition"
      (callNames.map Atom.var) [TypeDefinitionConstruction.result input constants predicate witness.ty texts]
      rfl (by decide) rfl returned
  have armReturned : BoundCalls.PureReturns program chosen state arm state
      (TypeDefinitionConstruction.result input constants predicate witness.ty texts) := by
    rw [arm_shape]
    apply BoundCalls.let_returns program chosen captured state state state (.var "extension")
      (.symbol "hol-light:type-definition") capturedCall (.symbol "hol-light:type-definition") _
      (BoundCalls.symbol_returns program chosen state "hol-light:type-definition") _ capturedReturned
    simp [captured, chosen, environment, ProofEvents.environment,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  let before := ProofEvents.stepEnvironment input.operators input.declarations input.axioms input.key
    (command input) input.cache input.receipts
  have dispatched : BoundCalls.PureReturns program before state
      (.expression [.symbol "hol-light:dispatch", .var "state", .var "key", .var "request"]) state
      (TypeDefinitionConstruction.result input constants predicate witness.ty texts) := by
    apply BoundCalls.authored_variable_call_returns program before
      (ProofEvents.environment (world input) input.key (command input)) state state "hol-light:dispatch"
      ["state", "key", "request"] ProofEvents.dispatchEquation.body _
      (by decide) (by decide) (by decide) _ _ (by decide)
    · simpa [before, ProofEvents.stepEnvironment, ProofEvents.environment, world, applySubst, Subst.lookup] using
        ProofEvents.dispatch_clause (world input) input.key (command input)
    · rw [ProofEvents.dispatch_shape]
      exact BoundCalls.case_returns program _ chosen state state state (.var "request") (command input) arm _ _
        ProofEvents.dispatchCases (Eval.read_cases_encoded ProofEvents.dispatchCases)
        (BoundCalls.variable_returns program _ state "request") (selected input) armReturned
  refine ⟨texts, ordered, ?_⟩
  have full := ProofEvents.authored_step_bound_dispatch_return input.operators input.declarations input.axioms input.key
    (command input) (TypeDefinitionConstruction.result input constants predicate witness.ty texts)
    input.cache input.receipts bindings state stateKey keyName requestName worldCaptured keyCaptured requestCaptured dispatched
  simpa only [receiptFresh, Bool.false_eq_true, ↓reduceIte] using full

end Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionEvents
