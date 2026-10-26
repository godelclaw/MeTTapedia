import Mettapedia.Languages.HOLLight.ExportCodec

/-!
# Selected source theories for the shared HOL receiver

The primitive HOL Light signature is registered independently of exported
proofs. A selected theory supplies a finite list of explicit commitments.
Reference definitions are admitted by the same definition gates as imported
proofs; their identities fix the vocabulary of those commitments. They do not
prepopulate the receiving proof cache or authorize further source axioms.

Logical derivations below are relative to these selected commitments. Their
interpretation in a model is a separate mathematical obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.SourceProfile

open Mettapedia.Languages.OpenTheory Mettapedia.Logic Lean
open DefinitionAdapters SignatureFormation ExportCodec

def sourceRevision : String := "924faf0c3471a04174ffdeb8576ce7cabcb92d64"

def individualOperator : TypeOp := .mk (Name.global "ind") .undefined

/-- The source's nullary individual type, with its full operator identity. -/
def individualBase : AtomicTy :=
  ⟨.op individualOperator [], by constructor <;> decide +kernel⟩

theorem individual_toHOL : (Ty.op individualOperator []).toHOL = .base individualBase :=
  Ty.toHOL_of_isAtomic individualBase.property

def individualContext : TheoryContext :=
  ContextControls.coreContext.addTypeOperator individualOperator 0
    (by simp [ContextControls.coreContext, ContextControls.baseContext,
      ContextControls.booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
      TheoryContext.empty, operatorName, individualOperator, TypeOp.bool, TypeOp.function,
      Name.global])

theorem core_includes_individual :
    ContextControls.coreContext.signature.Includes individualContext.signature :=
  ContextControls.coreContext.addTypeOperator_includes _ _ _

theorem selection_schema_formed :
    TypeFormed individualContext.signature
      (ModelInterpretation.selectionType (.var ContextControls.equalityParameter)) := by
  have functionRegistered : individualContext.signature.typeOperators TypeOp.function = some 2 :=
    core_includes_individual.1 _ _
      (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
  have booleanFormed : TypeFormed individualContext.signature Ty.bool :=
    ContextControls.boolean_formed.mono
      (ContextControls.core_includes.trans core_includes_individual)
  exact TypeFormed.function _ functionRegistered
    (TypeFormed.function _ functionRegistered (by simp [TypeFormed]) booleanFormed)
    (by simp [TypeFormed])

def primitiveContext : TheoryContext :=
  individualContext.addConstant ModelInterpretation.selectionConstant
    (ModelInterpretation.selectionType (.var ContextControls.equalityParameter))
    selection_schema_formed
    (by simp [individualContext, ContextControls.coreContext, ContextControls.baseContext,
      ContextControls.booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
      TheoryContext.empty, constantName, ModelInterpretation.selectionConstant, Const.equality,
      Name.global])

theorem individual_includes : individualContext.signature.Includes primitiveContext.signature :=
  individualContext.addConstant_includes _ _ selection_schema_formed _

theorem selector_registered :
    primitiveContext.signature.constants ModelInterpretation.selectionConstant =
      some (ModelInterpretation.selectionType (.var ContextControls.equalityParameter)) :=
  individualContext.addConstant_registered _ _ selection_schema_formed _

def primitiveBasis : ExportCodec.State :=
  { received := ExportReplay.empty primitiveContext
    symbols := ⟨[("fun", TypeOp.function), ("bool", TypeOp.bool),
      ("ind", individualOperator)],
      [("=", Const.equality), ("@", ModelInterpretation.selectionConstant)]⟩ }

structure Profile where
  identifier : String
  initial : ExportCodec.State
  reference : ExportCodec.State
  commitments : List Sequent

def Profile.policy (profile : Profile) : AxiomPolicy :=
  fun sequent => sequent ∈ profile.commitments

instance (profile : Profile) : DecidablePred profile.policy :=
  fun _ => inferInstanceAs (Decidable (_ ∈ profile.commitments))

/-- Only definitions may introduce the vocabulary of an explicit theory.
They pass through the existing registered calculus without any axiom policy. -/
def referenceDefinitions? : ExportCodec.State → List Json → Option ExportCodec.State
  | before, [] => some before
  | before, input :: rest =>
      if (field? input "rule").bind string? ≠ some "DEFINITION" then none else do
        let after ← ExportCodec.receive? emptyAxiomPolicy before input
        referenceDefinitions? after rest

theorem referenceDefinitions?_to_replay (before : ExportCodec.State) (inputs : List Json)
    (after : ExportCodec.State)
    (accepted : referenceDefinitions? before inputs = some after) :
    ExportCodec.receiveMany? emptyAxiomPolicy before inputs = some after := by
  induction inputs generalizing before with
  | nil => exact accepted
  | cons input inputs ih =>
    unfold referenceDefinitions? at accepted
    split at accepted
    · contradiction
    · cases next : ExportCodec.receive? emptyAxiomPolicy before input with
      | none => simp [next] at accepted
      | some middle =>
        have remaining : referenceDefinitions? middle inputs = some after := by
          simpa [next] using accepted
        simpa [ExportCodec.receiveMany?, next] using ih middle remaining

def commitment? (reference : ExportCodec.State) (json : Json) : Option Sequent := do
  let (sequent, source) ← sequent? reference.symbols json
  if sequent.hyp ≠ ∅ then none else do
    let checked ← checkSource reference.received.registered.context.signature
      (ExportReplay.instanceCertificates reference.received.registered.context.signature) source
    if checked.same sequent.concl ≠ true then none else
      pure sequent

/-- The caller selects this theory document separately from the proof file.
Proof exports cannot append entries to the resulting authorization policy. -/
def load? (basis : ExportCodec.State) (document : Json) : Option Profile := do
  if (← string? (← field? document "sourceRevision")) ≠ sourceRevision then none else do
    let identifier ← string? (← field? document "profile")
    let declarations ← array? (← field? document "definitions")
    let reference ← referenceDefinitions? basis declarations
    let commitments ← (← array? (← field? document "commitments")).mapM
      (commitment? reference)
    pure ⟨identifier, { basis with sourceOrigin := identifier }, reference, commitments⟩

/-- Every dependency of every received theorem belongs to the separately
selected theory, including after constant and type-definition extensions. -/
theorem received_dependencies (profile : Profile) (inputs : List Json)
    (after : ExportCodec.State)
    (valid : ExportReplay.Valid profile.policy profile.initial.received)
    (accepted : ExportCodec.receiveMany? profile.policy profile.initial inputs = some after)
    {id : Nat} {claim : Sequent} {fact : Theorem}
    (found : ExportReplay.root? after.received id claim = some fact) :
    ∀ commitment ∈ fact.axioms, commitment ∈ profile.commitments :=
  (ExportCodec.received_root_derivation profile.policy profile.initial inputs after
    valid accepted found).1.authorizedAxioms

theorem unlisted_axiom_refused (profile : Profile) (sequent : Sequent)
    (unlisted : sequent ∉ profile.commitments) :
    (RuleRequest.axiom sequent).check profile.policy = none := by
  simp [RuleRequest.check, Profile.policy, unlisted]

theorem listed_axiom_checked (profile : Profile) (sequent : Sequent)
    (listed : sequent ∈ profile.commitments) (hypothesisFree : sequent.hyp = ∅) :
    (RuleRequest.axiom sequent).check profile.policy = checkAxiom sequent := by
  simp [RuleRequest.check, Profile.policy, listed, hypothesisFree]

end Mettapedia.Languages.HOLLight.SourceProfile
