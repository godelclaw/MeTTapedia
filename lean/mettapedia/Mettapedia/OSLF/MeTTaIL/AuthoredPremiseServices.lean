import Mettapedia.GSLT.LanguageDef.GeneralPremiseReceiptWire
import Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeDiscovery
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

/-!
# Source services for original finite authored firing receipts

Requests and evidence use the existing physical wire-data language. The fixed authorization retains the full original finite Plan,
source bound context, result type, scope and handler registry coordinate.
The actual dynamic handler is an indexed service parameter; no string or
hash in the packet establishes function identity. Source acceptance is
proved against the original receipt/source semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralPremise GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef
open SemanticService
open KernelAuthority SemanticEvidence

abbrev Claim := GeneralPremiseNativeEvidence.Claim
abbrev Proof := GeneralRuleJobs.Receipt
abbrev Header := GeneralPremiseReceiptWire.Header

/-- The common physical string carries canonical finite-alphabet data. -/
def objectWire {Value : Type} (codec : Codec Value) (value : Value) : CettaWire.Term :=
  .string (Binary.Text.render (Binary.encodeWith codec value))

def readObject? {Value : Type} (codec : Codec Value) : CettaWire.Term → Option Value
  | .string text => do
      let word ← Binary.Text.parse text
      let value ← Binary.canonicalDecodeWith codec word
      if text = Binary.Text.render (Binary.encodeWith codec value) then some value else none
  | _ => none

theorem readObject?_objectWire {Value : Type} (codec : Codec Value) (value : Value) :
    readObject? codec (objectWire codec value) = some value := by
  simp only [readObject?, objectWire, Binary.Text.parse_render,
    Binary.canonicalDecodeWith_encodeWith, Bind.bind, Option.bind, ite_true]

theorem readObject?_exact {Value : Type} (codec : Codec Value)
    (wire : CettaWire.Term) (value : Value) :
    readObject? codec wire = some value ↔ wire = objectWire codec value := by
  constructor
  · intro accepted
    cases wire with
    | symbol name => cases accepted
    | natural number => cases accepted
    | application head args => cases accepted
    | string text =>
      cases parsed : Binary.Text.parse text with
      | none => simp only [readObject?, parsed, Bind.bind, Option.bind] at accepted; cases accepted
      | some word =>
        cases read : Binary.canonicalDecodeWith codec word with
        | none => simp only [readObject?, parsed, read, Bind.bind, Option.bind] at accepted; cases accepted
        | some found =>
          simp only [readObject?, parsed, read, Bind.bind, Option.bind] at accepted
          split at accepted
          · rename_i same
            cases Option.some.inj accepted
            exact congrArg CettaWire.Term.string same
          · cases accepted
  · intro same
    rw [same]
    exact readObject?_objectWire codec value

def headerEqual (first second : Header) : Bool :=
  decide (GeneralPremiseReceiptWire.headerCodec.put first = GeneralPremiseReceiptWire.headerCodec.put second)

theorem headerEqual_exact (first second : Header) : headerEqual first second = true ↔ first = second := by
  simp only [headerEqual, decide_eq_true_eq, GeneralPremiseReceiptWire.headerCodec.put_injective.eq_iff]

def requestTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : CettaWire.Term :=
  objectWire GeneralPremiseReceiptWire.requestCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, claim)

def proofTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (proof : Proof) : CettaWire.Term :=
  objectWire GeneralPremiseReceiptWire.proofCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, proof)

def readRequest? (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : CettaWire.Term) : Option Claim := do
  let value ← readObject? GeneralPremiseReceiptWire.requestCodec native
  if headerEqual value.1 (GeneralPremiseReceiptWire.header scope handler plan bound type) then some value.2 else none

def readProof? (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : CettaWire.Term) : Option Proof := do
  let value ← readObject? GeneralPremiseReceiptWire.proofCodec native
  if headerEqual value.1 (GeneralPremiseReceiptWire.header scope handler plan bound type) then some value.2 else none

theorem readRequest?_exact (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : CettaWire.Term) (claim : Claim) :
    readRequest? scope handler plan bound type native = some claim ↔ native = requestTerm scope handler plan bound type claim := by
  constructor
  · intro accepted
    cases read : readObject? GeneralPremiseReceiptWire.requestCodec native with
    | none => simp only [readRequest?, read, Bind.bind, Option.bind] at accepted; cases accepted
    | some value =>
        simp only [readRequest?, read, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i same
          have header := (headerEqual_exact _ _).mp same
          have represented := (readObject?_exact _ _ _).mp read
          have content := Option.some.inj accepted
          have pair : value = (GeneralPremiseReceiptWire.header scope handler plan bound type, claim) :=
            Prod.ext header content
          rw [pair] at represented
          exact represented
        · cases accepted
  · intro same
    simp only [same, readRequest?, requestTerm, readObject?_objectWire, Bind.bind, Option.bind]
    rw [(headerEqual_exact _ _).mpr rfl]
    rfl

theorem readProof?_exact (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : CettaWire.Term) (proof : Proof) :
    readProof? scope handler plan bound type native = some proof ↔ native = proofTerm scope handler plan bound type proof := by
  constructor
  · intro accepted
    cases read : readObject? GeneralPremiseReceiptWire.proofCodec native with
    | none => simp only [readProof?, read, Bind.bind, Option.bind] at accepted; cases accepted
    | some value =>
        simp only [readProof?, read, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i same
          have header := (headerEqual_exact _ _).mp same
          have represented := (readObject?_exact _ _ _).mp read
          have content := Option.some.inj accepted
          have pair : value = (GeneralPremiseReceiptWire.header scope handler plan bound type, proof) :=
            Prod.ext header content
          rw [pair] at represented
          exact represented
        · cases accepted
  · intro same
    simp only [same, readProof?, proofTerm, readObject?_objectWire, Bind.bind, Option.bind]
    rw [(headerEqual_exact _ _).mpr rfl]
    rfl

/-- Independent original source meaning on the literal native request image. -/
def Meaning (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) : Prop :=
  ∃ claim : Claim, native = requestTerm scope handler plan bound type claim ∧
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim

def target (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : AdmissionObject where
  Carrier := CettaWire.Term
  Meaning := Meaning scope handler dynamic plan bound type

/-- Native evidence is actual declared data syntax. Its original receipt
meaning is independent of the implementation of the native reader/checker. -/
def guest (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : NativeProofSystem CettaWire.Term where
  ProofObject := CettaWire.Term
  Judges nativeProof native := ∃ (claim : Claim) (proof : Proof),
    native = requestTerm scope handler plan bound type claim ∧
    nativeProof = proofTerm scope handler plan bound type proof ∧
    proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2

def check (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr)
    (native nativeProof : CettaWire.Term) : Bool :=
  match readRequest? scope handler plan bound type native,
      readProof? scope handler plan bound type nativeProof with
  | some claim, some proof => GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof
  | _, _ => false

theorem check_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : CettaWire.Term) :
    check scope handler dynamic plan bound type native nativeProof = true ↔
      (guest scope handler dynamic plan bound type).Judges nativeProof native := by
  constructor
  · intro checked
    cases requestRead : readRequest? scope handler plan bound type native with
    | none => simp only [check, requestRead] at checked; cases checked
    | some claim =>
        cases proofRead : readProof? scope handler plan bound type nativeProof with
        | none => simp only [check, requestRead, proofRead] at checked; cases checked
        | some proof =>
            have valid := (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp
              (by simpa only [check, requestRead, proofRead] using checked)
            exact ⟨claim, proof, (readRequest?_exact scope handler plan bound type native claim).mp requestRead,
              (readProof?_exact scope handler plan bound type nativeProof proof).mp proofRead, valid⟩
  · rintro ⟨claim, proof, inputAt, proofAt, valid⟩
    have requestRead := (readRequest?_exact scope handler plan bound type native claim).mpr inputAt
    have proofRead := (readProof?_exact scope handler plan bound type nativeProof proof).mpr proofAt
    simp only [check, requestRead, proofRead]
    exact (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mpr valid

def kernel (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : NativeProofKernel (guest scope handler dynamic plan bound type) where
  decide := check scope handler dynamic plan bound type
  correct := check_exact scope handler dynamic plan bound type

theorem meaning_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) :
    Meaning scope handler dynamic plan bound type native ↔
      Nonempty ((guest scope handler dynamic plan bound type).ProofFibre native) := by
  constructor
  · rintro ⟨claim, inputAt, proof, valid⟩
    exact ⟨⟨proofTerm scope handler plan bound type proof, claim, proof, inputAt, rfl, valid⟩⟩
  · rintro ⟨⟨nativeProof, claim, proof, inputAt, _, valid⟩⟩
    exact ⟨claim, inputAt, proof, valid⟩

def service (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : SemanticService.Service (target scope handler dynamic plan bound type) :=
  .nativeProof (guest scope handler dynamic plan bound type) (kernel scope handler dynamic plan bound type)
    (meaning_exact scope handler dynamic plan bound type)

def invocation (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : CettaWire.Term) :
    SemanticServiceInvocation.Request (service scope handler dynamic plan bound type) := .nativeProof native nativeProof

theorem invocation_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : CettaWire.Term) :
    (SemanticServiceInvocation.invoke
      (invocation scope handler dynamic plan bound type native nativeProof)).acceptedValue = some native ↔
        (guest scope handler dynamic plan bound type).Judges nativeProof native := by
  change (if check scope handler dynamic plan bound type native nativeProof then some native else none) = some native ↔ _
  rw [← check_exact]
  cases check scope handler dynamic plan bound type native nativeProof <;> simp

theorem check_source (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof) :
    check scope handler dynamic plan bound type (requestTerm scope handler plan bound type claim)
      (proofTerm scope handler plan bound type proof) =
        GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof := by
  simp only [check, (readRequest?_exact scope handler plan bound type _ claim).mpr rfl,
    (readProof?_exact scope handler plan bound type _ proof).mpr rfl]

theorem source_iff_native_service (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔ ∃ proof : Proof,
      (SemanticServiceInvocation.invoke (invocation scope handler dynamic plan bound type
        (requestTerm scope handler plan bound type claim) (proofTerm scope handler plan bound type proof))).acceptedValue =
          some (requestTerm scope handler plan bound type claim) := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨proof, (invocation_exact scope handler dynamic plan bound type _ _).mpr
      ⟨claim, proof, rfl, rfl, valid⟩⟩
  · rintro ⟨proof, accepted⟩
    obtain ⟨actualClaim, actualProof, requestAt, _, valid⟩ :=
      (invocation_exact scope handler dynamic plan bound type
        (requestTerm scope handler plan bound type claim) (proofTerm scope handler plan bound type proof)).mp accepted
    have readAt := congrArg (readRequest? scope handler plan bound type) requestAt
    rw [(readRequest?_exact scope handler plan bound type _ claim).mpr rfl,
      (readRequest?_exact scope handler plan bound type _ actualClaim).mpr rfl] at readAt
    cases Option.some.inj readAt
    exact ⟨actualProof, valid⟩

open SemanticService

def requiredInterface (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : Interface (target scope handler dynamic plan bound type) :=
  .nativeProof (guest scope handler dynamic plan bound type)

theorem service_interface_matches (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) :
    InterfaceMatches (RawService.erase (service scope handler dynamic plan bound type))
      (requiredInterface scope handler dynamic plan bound type) := .nativeProof _ _

/-- The callable role is literal protocol data. The installed handler remains
fixed by the indexed service, rather than selected by this caller's label. -/
def serviceHead : String := "GSLT.AuthoredFiring.v1"

def invokeRouted (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (requested : String)
    (native nativeProof : CettaWire.Term) : Option CettaWire.Term :=
  if requested = serviceHead then
    (SemanticServiceInvocation.invoke
      (invocation scope handler dynamic plan bound type native nativeProof)).acceptedValue
  else none

theorem routed_accepted_iff (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (requested : String)
    (native nativeProof output : CettaWire.Term) :
    invokeRouted scope handler dynamic plan bound type requested native nativeProof = some output ↔
      requested = serviceHead ∧ native = output ∧
        (guest scope handler dynamic plan bound type).Judges nativeProof native := by
  change (if requested = serviceHead then
    (if check scope handler dynamic plan bound type native nativeProof then some native else none) else none) = some output ↔ _
  by_cases role : requested = serviceHead
  · rw [if_pos role]
    cases checked : check scope handler dynamic plan bound type native nativeProof with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨_, _, valid⟩
        have accepted := (check_exact scope handler dynamic plan bound type native nativeProof).mpr valid
        rw [checked] at accepted
        cases accepted
    | true =>
        simp only [↓reduceIte, Option.some.injEq]
        exact ⟨fun same => ⟨role, same,
          (check_exact scope handler dynamic plan bound type native nativeProof).mp checked⟩,
          fun valid => valid.2.1⟩
  · rw [if_neg role]
    simp only [reduceCtorEq, false_iff]
    intro valid
    exact role valid.1

theorem wrong_role_refused (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (requested : String)
    (native nativeProof : CettaWire.Term) (wrong : requested ≠ serviceHead) :
    invokeRouted scope handler dynamic plan bound type requested native nativeProof = none := by
  change (if requested = serviceHead then
    (if check scope handler dynamic plan bound type native nativeProof then some native else none) else none) = none
  rw [if_neg wrong]

/-- Application and both argument objects use the actual existing declared
physical wire constructors. The role is operational service selection, never a
new equation of the ambient native conversion relation. -/
def callWire (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : CettaWire.Term :=
  .application serviceHead
    [objectWire GeneralPremiseReceiptWire.requestCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, claim),
     objectWire GeneralPremiseReceiptWire.proofCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, proof)]

def runCall? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : CettaWire.Term → Option CettaWire.Term
  | .application requested [request, proof] =>
      invokeRouted scope handler dynamic plan bound type requested request proof
  | _ => none

theorem runCall?_source (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof) :
    runCall? scope handler dynamic plan bound type (callWire scope handler plan bound type claim proof) =
      some (requestTerm scope handler plan bound type claim) ↔
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  simp only [runCall?, callWire]
  change invokeRouted scope handler dynamic plan bound type serviceHead
    (requestTerm scope handler plan bound type claim) (proofTerm scope handler plan bound type proof) =
      some (requestTerm scope handler plan bound type claim) ↔ _
  rw [routed_accepted_iff]
  simp only [true_and]
  rw [← check_exact, check_source, GeneralPremiseNativeEvidence.check_exact]

/-- Accepted calls reflect the exact literal source request and the exact
original receipt, including all header and evidence bytes represented there. -/
theorem runCall?_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input output : CettaWire.Term) :
    runCall? scope handler dynamic plan bound type input = some output ↔
      ∃ (claim : Claim) (proof : Proof),
        input = callWire scope handler plan bound type claim proof ∧
        output = requestTerm scope handler plan bound type claim ∧
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  constructor
  · intro accepted
    cases input with
    | symbol name => cases accepted
    | string text => cases accepted
    | natural number => cases accepted
    | application role args =>
      cases args with
      | nil => cases accepted
      | cons request args =>
        cases args with
        | nil => cases accepted
        | cons submitted args =>
          cases args with
          | cons extra rest => cases accepted
          | nil =>
            obtain ⟨roleAt, outputAt, claim, proof, requestAt, proofAt, valid⟩ :=
              (routed_accepted_iff scope handler dynamic plan bound type role request submitted output).mp accepted
            refine ⟨claim, proof, ?_, outputAt.symm.trans requestAt, valid⟩
            rw [roleAt, requestAt, proofAt]
            rfl
  · rintro ⟨claim, proof, rfl, rfl, valid⟩
    exact (runCall?_source scope handler dynamic plan bound type claim proof).mpr valid

/-- Unrestricted original finite receipt evidence has executable native
calls, and an accepted native call cannot invent an original source firing. -/
theorem source_iff_native_call (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔ ∃ proof : Proof,
      runCall? scope handler dynamic plan bound type (callWire scope handler plan bound type claim proof) =
        some (requestTerm scope handler plan bound type claim) := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨proof, (runCall?_source scope handler dynamic plan bound type claim proof).mpr valid⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨proof, (runCall?_source scope handler dynamic plan bound type claim proof).mp accepted⟩

namespace External

/-- The profile is authorized independently of the submitted request. -/
def profileCodec : Codec Header := GeneralPremiseReceiptWire.headerCodec

def encodeCall (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : List Binary.Alphabet :=
  Binary.encodeWith BindingSyntax.Wire.physicalCodec (callWire scope handler plan bound type claim proof)

def replyHead : String := "GSLT.AuthoredFiring.Reply.v1"

def replyWire (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : CettaWire.Term :=
  .application replyHead
    [callWire scope handler plan bound type claim proof,
     objectWire GeneralPremiseReceiptWire.requestCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, claim)]

def encodeReply (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : List Binary.Alphabet :=
  Binary.encodeWith BindingSyntax.Wire.physicalCodec (replyWire scope handler plan bound type claim proof)

/-- Parse canonical bytes, execute the actual native call and retain its
original complete request beside the checked result. -/
def run (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input : List Binary.Alphabet) : Option (List Binary.Alphabet) := do
  let wire ← Binary.canonicalDecodeWith BindingSyntax.Wire.physicalCodec input
  let native ← runCall? scope handler dynamic plan bound type wire
  let output ← some native
  return Binary.encodeWith BindingSyntax.Wire.physicalCodec (.application replyHead [wire, output])

theorem run_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input output : List Binary.Alphabet) :
    run scope handler dynamic plan bound type input = some output ↔
      ∃ (claim : Claim) (proof : Proof),
        input = encodeCall scope handler plan bound type claim proof ∧
        output = encodeReply scope handler plan bound type claim proof ∧
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  constructor
  · intro accepted
    cases decoded : Binary.canonicalDecodeWith BindingSyntax.Wire.physicalCodec input with
    | none => simp only [run, decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some wire =>
        cases called : runCall? scope handler dynamic plan bound type wire with
        | none => simp only [run, decoded, called, Bind.bind, Option.bind] at accepted; cases accepted
        | some native =>
            obtain ⟨claim, proof, callAt, outputAt, valid⟩ :=
              (runCall?_exact scope handler dynamic plan bound type wire native).mp called
            have wireAt : wire = callWire scope handler plan bound type claim proof :=
              callAt
            have inputAt := (Binary.canonicalDecodeWith_exact BindingSyntax.Wire.physicalCodec input wire).mp decoded
            rw [wireAt] at inputAt
            refine ⟨claim, proof, inputAt.symm, ?_, valid⟩
            simp only [run, decoded, called, Bind.bind, Option.bind] at accepted
            rw [outputAt] at accepted
            simp only [requestTerm, objectWire] at accepted
            cases Option.some.inj accepted
            rw [wireAt]
            rfl
  · rintro ⟨claim, proof, inputAt, outputAt, valid⟩
    have called := (runCall?_source scope handler dynamic plan bound type claim proof).mpr valid
    rw [inputAt, outputAt]
    simp only [run, encodeCall, Binary.canonicalDecodeWith_encodeWith, Bind.bind, Option.bind]
    change (do
      let native ← runCall? scope handler dynamic plan bound type (callWire scope handler plan bound type claim proof)
      let output ← some native
      return Binary.encodeWith BindingSyntax.Wire.physicalCodec
        (.application replyHead [callWire scope handler plan bound type claim proof, output])) = _
    rw [called]
    simp only [Bind.bind, Option.bind, requestTerm, objectWire]
    rfl

/-- Original source receipts have canonical accepted byte packets, including
recursive declarations. This theorem does not enumerate source proofs. -/
theorem source_iff_run (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔ ∃ proof : Proof,
      run scope handler dynamic plan bound type (encodeCall scope handler plan bound type claim proof) =
        some (encodeReply scope handler plan bound type claim proof) := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨proof, (run_exact scope handler dynamic plan bound type _ _).mpr ⟨claim, proof, rfl, rfl, valid⟩⟩
  · rintro ⟨proof, accepted⟩
    obtain ⟨actualClaim, actualProof, inputAt, _, valid⟩ :=
      (run_exact scope handler dynamic plan bound type _ _).mp accepted
    have wireAt := Binary.encodeWith_injective BindingSyntax.Wire.physicalCodec inputAt
    have inputNativeAt : requestTerm scope handler plan bound type claim = requestTerm scope handler plan bound type actualClaim := by
      have args := (CettaWire.Term.application.inj wireAt).2
      have first := (List.cons.inj args).1
      exact first
    have readAt := congrArg (readRequest? scope handler plan bound type) inputNativeAt
    rw [(readRequest?_exact scope handler plan bound type _ claim).mpr rfl,
      (readRequest?_exact scope handler plan bound type _ actualClaim).mpr rfl] at readAt
    cases Option.some.inj readAt
    exact ⟨actualProof, valid⟩

end External

namespace Discovery

abbrev Query := Claim × List Nat
abbrev Article := GeneralPremiseNativeDiscovery.Article
abbrev State := GeneralPremiseNativeDiscovery.State
abbrev Result := Query × Nat × List Article

/-- A schedule carries only slot budgets. It never supplies proposed evidence
or a caller-created cursor/journal checkpoint. -/
def budgetCodec : Codec (List Nat) := Codec.list Codec.nat

def serviceHead : String := "GSLT.AuthoredDiscovery.v1"

def callWire (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) : CettaWire.Term :=
  .application serviceHead [
    objectWire GeneralPremiseReceiptWire.requestCodec
      (GeneralPremiseReceiptWire.header scope handler plan bound type, query.1),
    objectWire budgetCodec query.2]

/-- The source request uses the existing full-Plan/header reader. The second
argument is a finite budget schedule; extra arguments or wrong roles refuse. -/
def readInput? (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : CettaWire.Term → Option Query
  | .application requested [request, budgets] =>
      if requested = serviceHead then do
        let claim ← readRequest? scope handler plan bound type request
        let schedule ← readObject? budgetCodec budgets
        return (claim, schedule)
      else none
  | _ => none

theorem readInput?_exact (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (input : CettaWire.Term) (query : Query) :
    readInput? scope handler plan bound type input = some query ↔
      input = callWire scope handler plan bound type query := by
  constructor
  · intro accepted
    cases input with
    | symbol name => cases accepted
    | string text => cases accepted
    | natural number => cases accepted
    | application requested args =>
      cases args with
      | nil => cases accepted
      | cons request args =>
        cases args with
        | nil => cases accepted
        | cons budgets args =>
          cases args with
          | cons extra rest => cases accepted
          | nil =>
            simp only [readInput?] at accepted
            split at accepted
            · rename_i role
              cases claimRead : readRequest? scope handler plan bound type request with
              | none => simp only [claimRead, Bind.bind, Option.bind] at accepted; cases accepted
              | some claim =>
                cases scheduleRead : readObject? budgetCodec budgets with
                | none => simp only [claimRead, scheduleRead, Bind.bind, Option.bind] at accepted; cases accepted
                | some schedule =>
                  simp only [claimRead, scheduleRead, Bind.bind, Option.bind, pure, Option.some.injEq] at accepted
                  have requestAt := (readRequest?_exact scope handler plan bound type request claim).mp claimRead
                  have budgetsAt := (readObject?_exact budgetCodec budgets schedule).mp scheduleRead
                  rw [← accepted, role, requestAt, budgetsAt]
                  rfl
            · cases accepted
  · intro same
    rw [same]
    simp only [readInput?, callWire, ite_true]
    change (do
      let claim ← readRequest? scope handler plan bound type (requestTerm scope handler plan bound type query.1)
      let schedule ← readObject? budgetCodec (objectWire budgetCodec query.2)
      return (claim, schedule)) = some query
    rw [(readRequest?_exact scope handler plan bound type _ query.1).mpr rfl,
      readObject?_objectWire]
    rfl

def Endpoints (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) : Prop :=
  (WellSorted.HasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.1 type ∧
    WellSorted.isObjectPattern claim.1 = true) ∧
  (WellSorted.HasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.2 type ∧
    WellSorted.isObjectPattern claim.2 = true)

def checkEndpoints (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) : Bool :=
  (WellSorted.checkHasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.1 type &&
    WellSorted.isObjectPattern claim.1) &&
  (WellSorted.checkHasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free bound claim.2 type &&
    WellSorted.isObjectPattern claim.2)

theorem checkEndpoints_exact (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    checkEndpoints plan bound type claim = true ↔ Endpoints plan bound type claim := by
  simp only [checkEndpoints, Bool.and_eq_true, Endpoints]
  constructor
  · rintro ⟨⟨first, firstObject⟩, second, secondObject⟩
    exact ⟨⟨WellSorted.checkHasType_sound first, firstObject⟩,
      WellSorted.checkHasType_sound second, secondObject⟩
  · rintro ⟨⟨first, firstObject⟩, second, secondObject⟩
    exact ⟨⟨WellSorted.checkHasType_complete_of_object first firstObject, firstObject⟩,
      WellSorted.checkHasType_complete_of_object second secondObject, secondObject⟩

theorem original_endpoints (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (result : proof.target = claim.2) :
    Endpoints plan bound type claim :=
  ⟨⟨valid.1.2.source_typed, valid.1.2.source_object⟩,
    result ▸ valid.2.2.2.2.1, result ▸ valid.2.2.2.2.2.2.1⟩

/-- Each slice executes the existing native resume operation's actual raw
function, using the state reached by the preceding slice. -/
def advance (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : List Nat → State → State
  | [], state => state
  | budget :: later, state =>
      advance dynamic plan bound type claim later
        ((GeneralPremiseNativeDiscovery.resumeOperation dynamic plan bound type).run (claim, budget, state)).2.2

theorem advance_eq_resume (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (budgets : List Nat) (state : State) :
    advance dynamic plan bound type claim budgets state =
      GeneralPremiseNativeDiscovery.resume dynamic plan bound type claim budgets.sum state := by
  induction budgets generalizing state with
  | nil => rfl
  | cons budget later ih =>
      rw [advance, ih]
      exact (GeneralPremiseNativeDiscovery.resume_add dynamic plan bound type claim budget later.sum state).symm

def generate (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) : State :=
  advance dynamic plan bound type query.1 query.2 GeneralPremiseNativeDiscovery.initial

theorem generate_eq_search (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) :
    generate dynamic plan bound type query = GeneralPremiseNativeDiscovery.search dynamic plan bound type query.1 query.2.sum :=
  advance_eq_resume dynamic plan bound type query.1 query.2 GeneralPremiseNativeDiscovery.initial

theorem generate_reached (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) :
    GeneralPremiseNativeDiscovery.StateReached dynamic plan bound type query.1 (generate dynamic plan bound type query) := by
  rw [generate_eq_search]
  exact GeneralPremiseNativeDiscovery.search_reached dynamic plan bound type query.1 query.2.sum

/-- No slice changes a source proof's inner events. Resuming appends search
slots; the complete-article journal equals one run at the summed budget. -/
theorem schedule_append (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (first second : List Nat) :
    generate dynamic plan bound type (claim, first ++ second) =
      advance dynamic plan bound type claim second (generate dynamic plan bound type (claim, first)) := by
  simp only [generate, advance_eq_resume, List.sum_append]
  exact GeneralPremiseNativeDiscovery.resume_add dynamic plan bound type claim first.sum second.sum GeneralPremiseNativeDiscovery.initial

def resultCodec : Codec (Header × Result) :=
  Codec.prod GeneralPremiseReceiptWire.headerCodec
    (Codec.prod (Codec.prod GeneralPremiseReceiptWire.claimCodec budgetCodec)
      (Codec.prod Codec.nat (Codec.list (Codec.list (Codec.fin 5)))))

def resultTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (result : Result) : CettaWire.Term :=
  objectWire resultCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, result)

def generatedResult (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) : Result :=
  let state := generate dynamic plan bound type query
  (query, state.cursor, state.articles)

/-- Run only the literal selected profile and admitted object endpoints.
An empty generated journal is still a successful unknown search result. -/
def run? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) : Option CettaWire.Term := do
  let query ← readInput? scope handler plan bound type native
  if checkEndpoints plan bound type query.1 then
    some (resultTerm scope handler plan bound type (generatedResult dynamic plan bound type query))
  else none

theorem run?_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native output : CettaWire.Term) :
    run? scope handler dynamic plan bound type native = some output ↔ ∃ query : Query,
      native = callWire scope handler plan bound type query ∧ Endpoints plan bound type query.1 ∧
      output = resultTerm scope handler plan bound type (generatedResult dynamic plan bound type query) := by
  constructor
  · intro accepted
    cases read : readInput? scope handler plan bound type native with
    | none => simp only [run?, read, Bind.bind, Option.bind] at accepted; cases accepted
    | some query =>
        simp only [run?, read, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i checked
          exact ⟨query, (readInput?_exact scope handler plan bound type native query).mp read,
            (checkEndpoints_exact plan bound type query.1).mp checked, (Option.some.inj accepted).symm⟩
        · cases accepted
  · rintro ⟨query, rfl, admitted, rfl⟩
    rw [run?, (readInput?_exact scope handler plan bound type _ query).mpr rfl]
    simp only [Bind.bind, Option.bind, (checkEndpoints_exact plan bound type query.1).mpr admitted, ite_true]

/-- Target authority is original finite receipt validity, not the search
Boolean. The literal complete article bytes retain every source occurrence. -/
def ResultMeaning (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (result : Result) : Prop :=
  Endpoints plan bound type result.1.1 ∧ result.2.1 = result.1.2.sum ∧ result.2.2.Nodup ∧
    ∀ article ∈ result.2.2, ∃ proof : Proof,
      article = GeneralPremiseReceiptWire.encodeReceipt proof ∧
      proof.ValidWith dynamic plan bound type result.1.1.1 ∧ proof.target = result.1.1.2

theorem generatedResult_meaning (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) (admitted : Endpoints plan bound type query.1) :
    ResultMeaning dynamic plan bound type (generatedResult dynamic plan bound type query) := by
  have reached := generate_reached dynamic plan bound type query
  have nodup := FiniteCertificateSearch.Retained.reachable_nodup _ _ _ _ reached
  have sound := FiniteCertificateSearch.Retained.reachable_sound _ _ _ _ reached
  refine ⟨admitted, ?_, nodup, ?_⟩
  · change (generate dynamic plan bound type query).cursor = query.2.sum
    rw [generate_eq_search, GeneralPremiseNativeDiscovery.search, GeneralPremiseNativeDiscovery.resume_cursor]
    exact Nat.zero_add _
  · intro article found
    exact (GeneralPremiseNativeDiscovery.articleCheck_exact dynamic plan bound type query.1 article).mp (sound article found)

def source (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : AdmissionObject where
  Carrier := CettaWire.Term
  Meaning native := ∃ query : Query,
    native = callWire scope handler plan bound type query ∧ Endpoints plan bound type query.1

def target (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : AdmissionObject where
  Carrier := Option CettaWire.Term
  Meaning output := ∃ result : Result,
    output = some (resultTerm scope handler plan bound type result) ∧ ResultMeaning dynamic plan bound type result

/-- This native operation actually generates its result; it accepts no
proposed proof. Raw malformed inputs return none without a semantic claim. -/
def operation (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) :
    AdmissionHom (source scope handler plan bound type) (target scope handler dynamic plan bound type) where
  run := run? scope handler dynamic plan bound type
  preserves native admitted := by
    obtain ⟨query, represented, endpoints⟩ := admitted
    exact ⟨generatedResult dynamic plan bound type query,
      (run?_exact scope handler dynamic plan bound type _ _).mpr ⟨query, represented, endpoints, rfl⟩,
      generatedResult_meaning dynamic plan bound type query endpoints⟩

def service (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) :
    SemanticService.Service.{0, 0} (target scope handler dynamic plan bound type) :=
  .nativeOperation (source scope handler plan bound type) (operation scope handler dynamic plan bound type)

def invocation (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) :
    SemanticServiceInvocation.Request (service scope handler dynamic plan bound type) := .nativeOperation native

def requiredInterface (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : Interface (target scope handler dynamic plan bound type) :=
  .nativeOperation (source scope handler plan bound type)

theorem service_interface_matches (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) :
    InterfaceMatches (RawService.erase (service scope handler dynamic plan bound type))
      (requiredInterface scope handler dynamic plan bound type) := .nativeOperation _ _

/-- The routed call executes the actual declared native operation. A refused
packet is distinct from a produced native result with an empty journal. -/
def runCall? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) : Option CettaWire.Term :=
  (SemanticServiceInvocation.invoke (invocation scope handler dynamic plan bound type native)).acceptedValue.join

theorem runCall?_eq_run? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : CettaWire.Term) :
    runCall? scope handler dynamic plan bound type native = run? scope handler dynamic plan bound type native := rfl

theorem callWire_injective (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) : Function.Injective (callWire scope handler plan bound type) := by
  intro first second same
  have read := congrArg (readInput? scope handler plan bound type) same
  rw [(readInput?_exact scope handler plan bound type _ first).mpr rfl,
    (readInput?_exact scope handler plan bound type _ second).mpr rfl] at read
  exact Option.some.inj read

/-- Every internally created checkpoint authorizes the existing resume
service for the same literal goal/profile. No external journal is admitted. -/
theorem resume_input_admitted (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) (next : Nat) (admitted : Endpoints plan bound type query.1) :
    (GeneralPremiseNativeDiscovery.resumeSource dynamic plan bound type).Meaning
      (query.1, next, generate dynamic plan bound type query) :=
  ⟨⟨admitted.1.1, admitted.2.1⟩, generate_reached dynamic plan bound type query⟩

theorem generated_receipt (dynamic : DynamicProvider) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (result : proof.target = claim.2) :
    GeneralPremiseReceiptWire.encodeReceipt proof ∈
      (generatedResult dynamic plan bound type (claim, [GeneralPremiseNativeDiscovery.discoveryBound proof])).2.2 := by
  have found := GeneralPremiseNativeDiscovery.receipt_discovered dynamic plan bound type claim proof valid result
  obtain ⟨article, stored, decoded⟩ := List.mem_filterMap.mp found
  have same := (GeneralPremiseReceiptWire.decodeReceipt_exact article proof).mp decoded
  change GeneralPremiseReceiptWire.encodeReceipt proof ∈
    (generate dynamic plan bound type (claim, [GeneralPremiseNativeDiscovery.discoveryBound proof])).articles
  rw [generate_eq_search]
  simpa only [List.sum_singleton, same] using stored

namespace External

def encodeCall (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Query) : List Binary.Alphabet :=
  Binary.encodeWith BindingSyntax.Wire.physicalCodec (callWire scope handler plan bound type query)

def replyHead : String := "GSLT.AuthoredDiscovery.Reply.v1"

def replyWire (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (result : Result) : CettaWire.Term :=
  .application replyHead [callWire scope handler plan bound type result.1,
    objectWire resultCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, result)]

def encodeReply (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (result : Result) : List Binary.Alphabet :=
  Binary.encodeWith BindingSyntax.Wire.physicalCodec (replyWire scope handler plan bound type result)

/-- Canonical requests invoke the actual native operation and return its
literal complete-article journal. The Boolean reports nonempty discovery;
false carries unknown, never source refutation. -/
def run (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input : List Binary.Alphabet) : Option (List Binary.Alphabet × Bool) := do
  let wire ← Binary.canonicalDecodeWith BindingSyntax.Wire.physicalCodec input
  let native ← runCall? scope handler dynamic plan bound type wire
  let result ← readObject? resultCodec native
  return (Binary.encodeWith BindingSyntax.Wire.physicalCodec
    (.application replyHead [wire, objectWire resultCodec result]), !result.2.2.2.isEmpty)

theorem run_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input : List Binary.Alphabet)
    (output : List Binary.Alphabet × Bool) :
    run scope handler dynamic plan bound type input = some output ↔ ∃ query : Query,
      input = encodeCall scope handler plan bound type query ∧ Endpoints plan bound type query.1 ∧
      output = (encodeReply scope handler plan bound type (generatedResult dynamic plan bound type query),
        !(generatedResult dynamic plan bound type query).2.2.isEmpty) := by
  constructor
  · intro accepted
    cases decoded : Binary.canonicalDecodeWith BindingSyntax.Wire.physicalCodec input with
    | none => simp only [run, decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some wire =>
        cases called : runCall? scope handler dynamic plan bound type wire with
        | none => simp only [run, decoded, called, Bind.bind, Option.bind] at accepted; cases accepted
        | some native =>
            obtain ⟨query, inputAt, admitted, resultAt⟩ :=
              (run?_exact scope handler dynamic plan bound type _ _).mp called
            have wireAt : wire = callWire scope handler plan bound type query :=
              inputAt
            have canonical := (Binary.canonicalDecodeWith_exact BindingSyntax.Wire.physicalCodec input wire).mp decoded
            refine ⟨query, ?_, admitted, ?_⟩
            · rw [wireAt] at canonical
              exact canonical.symm
            · simp only [run, decoded, called, Bind.bind, Option.bind] at accepted
              rw [resultAt] at accepted
              simp only [resultTerm, readObject?_objectWire] at accepted
              cases Option.some.inj accepted
              rw [wireAt]
              rfl
  · rintro ⟨query, inputAt, admitted, outputAt⟩
    have called : runCall? scope handler dynamic plan bound type (callWire scope handler plan bound type query) =
        some (resultTerm scope handler plan bound type (generatedResult dynamic plan bound type query)) := by
      rw [runCall?_eq_run?]
      exact (run?_exact scope handler dynamic plan bound type _ _).mpr ⟨query, rfl, admitted, rfl⟩
    rw [inputAt, outputAt]
    simp only [run, encodeCall, Binary.canonicalDecodeWith_encodeWith, Bind.bind, Option.bind]
    change (do
      let native ← runCall? scope handler dynamic plan bound type (callWire scope handler plan bound type query)
      let result ← readObject? resultCodec native
      return (Binary.encodeWith BindingSyntax.Wire.physicalCodec
        (.application replyHead [callWire scope handler plan bound type query, objectWire resultCodec result]),
        !result.2.2.2.isEmpty)) = _
    rw [called]
    simp only [Bind.bind, Option.bind, resultTerm, readObject?_objectWire]
    rfl

theorem run_source (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (query : Query) (admitted : Endpoints plan bound type query.1) :
    run scope handler dynamic plan bound type (encodeCall scope handler plan bound type query) =
      some (encodeReply scope handler plan bound type (generatedResult dynamic plan bound type query),
        !(generatedResult dynamic plan bound type query).2.2.isEmpty) :=
  (run_exact scope handler dynamic plan bound type _ _).mpr ⟨query, rfl, admitted, rfl⟩

/-- Every original finite receipt has a budget-only request that generates
its exact canonical article. Its proof is not an input to the operation. -/
theorem receipt_eventually_generated (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof)
    (valid : proof.ValidWith dynamic plan bound type claim.1) (result : proof.target = claim.2) :
    ∃ budgets : List Nat, ∃ generated : Result,
      run scope handler dynamic plan bound type (encodeCall scope handler plan bound type (claim, budgets)) =
        some (encodeReply scope handler plan bound type generated, true) ∧
      GeneralPremiseReceiptWire.encodeReceipt proof ∈ generated.2.2 ∧
      ResultMeaning dynamic plan bound type generated := by
  let budgets := [GeneralPremiseNativeDiscovery.discoveryBound proof]
  let generated := generatedResult dynamic plan bound type (claim, budgets)
  have found : GeneralPremiseReceiptWire.encodeReceipt proof ∈ generated.2.2 :=
    generated_receipt dynamic plan bound type claim proof valid result
  have nonempty : (!generated.2.2.isEmpty) = true := by
    rw [List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem found)]
    rfl
  have admitted := original_endpoints dynamic plan bound type claim proof valid result
  refine ⟨budgets, generated, ?_, found, generatedResult_meaning dynamic plan bound type _ admitted⟩
  have accepted := run_source scope handler dynamic plan bound type (claim, budgets) admitted
  change run scope handler dynamic plan bound type (encodeCall scope handler plan bound type (claim, budgets)) =
    some (encodeReply scope handler plan bound type generated, !generated.2.2.isEmpty) at accepted
  rw [nonempty] at accepted
  exact accepted

/-- Soundness reflects every complete article, with its inner history and
physical declaration/site provenance unchanged. -/
theorem accepted_articles (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input output : List Binary.Alphabet) (found : Bool)
    (accepted : run scope handler dynamic plan bound type input = some (output, found)) :
    ∃ query : Query, ∃ generated : Result,
      input = encodeCall scope handler plan bound type query ∧
      output = encodeReply scope handler plan bound type generated ∧ generated.1 = query ∧
      ResultMeaning dynamic plan bound type generated ∧ found = !generated.2.2.isEmpty := by
  obtain ⟨query, inputAt, admitted, outputAt⟩ := (run_exact scope handler dynamic plan bound type _ _).mp accepted
  have first := congrArg Prod.fst outputAt
  have second := congrArg Prod.snd outputAt
  exact ⟨query, generatedResult dynamic plan bound type query, inputAt, first, rfl,
    generatedResult_meaning dynamic plan bound type query admitted, second⟩

theorem source_iff_generated (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔
      ∃ budgets : List Nat, ∃ output,
        run scope handler dynamic plan bound type (encodeCall scope handler plan bound type (claim, budgets)) =
          some (output, true) := by
  constructor
  · rintro ⟨proof, valid, result⟩
    obtain ⟨budgets, generated, accepted, _, _⟩ :=
      receipt_eventually_generated scope handler dynamic plan bound type claim proof valid result
    exact ⟨budgets, _, accepted⟩
  · rintro ⟨budgets, output, accepted⟩
    obtain ⟨query, generated, inputAt, _, represented, meaningful, found⟩ :=
      accepted_articles scope handler dynamic plan bound type _ _ true accepted
    have wires := Binary.encodeWith_injective BindingSyntax.Wire.physicalCodec inputAt
    have queryAt := callWire_injective scope handler plan bound type
      wires
    have hasArticle : generated.2.2 ≠ [] := by
      intro empty
      rw [empty] at found
      cases found
    obtain ⟨article, stored⟩ := List.exists_mem_of_ne_nil _ hasArticle
    obtain ⟨proof, _, valid, result⟩ := meaningful.2.2.2 article stored
    have claimAt : generated.1.1 = claim := by rw [represented, ← queryAt]
    exact ⟨proof, claimAt ▸ valid, claimAt ▸ result⟩

end External

end Discovery

end Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices
