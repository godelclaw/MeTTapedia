import Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireData
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

/-!
# Optional declared-data representations of authored source services

The independent source packet engine is imported above. This optional
comparison attaches its requests and evidence to actual terms of the native
wire-data signature. The fixed authorization retains the full original finite Plan,
source bound context, result type, scope and handler registry coordinate.
The actual dynamic handler is an indexed service parameter; no string or
hash in the packet establishes function identity. Native acceptance is
proved against the original receipt/source semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseServices

open Mettapedia.OSLF.MeTTaIL
open Syntax GeneralPremise GeneralExecutionAdmission
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef
open SemanticService
open KernelAuthority SemanticEvidence
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

open Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices
  (Claim Proof Header objectWire headerEqual headerEqual_exact serviceHead callWire)

/-- Canonical binary data inhabits the existing declared native data type. -/
def nativeObject {Value : Type} {n : Nat} (codec : Codec Value) (value : Value) : Tower.Tm n :=
  NativeWireData.encode (objectWire codec value)

def readObject? {Value : Type} {n : Nat} (codec : Codec Value) (native : Tower.Tm n) : Option Value := do
  let wire ← NativeWireData.decode native
  let text ← match wire with | .string text => some text | _ => none
  let word ← Binary.Text.parse text
  let value ← Binary.canonicalDecodeWith codec word
  if native = nativeObject codec value then some value else none

theorem readObject?_nativeObject {Value : Type} {n : Nat} (codec : Codec Value) (value : Value) :
    readObject? codec (nativeObject (n := n) codec value) = some value := by
  simp only [readObject?, nativeObject, objectWire, NativeWireData.decode_encode,
    Binary.Text.parse_render, Binary.canonicalDecodeWith_encodeWith, Bind.bind, Option.bind, ite_true]

theorem readObject?_exact {Value : Type} {n : Nat} (codec : Codec Value)
    (native : Tower.Tm n) (value : Value) :
    readObject? codec native = some value ↔ native = nativeObject codec value := by
  constructor
  · intro accepted
    cases decoded : NativeWireData.decode native with
    | none => simp only [readObject?, decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some wire =>
        cases wire with
        | symbol name => simp only [readObject?, decoded, Bind.bind, Option.bind] at accepted; cases accepted
        | natural number => simp only [readObject?, decoded, Bind.bind, Option.bind] at accepted; cases accepted
        | application head args => simp only [readObject?, decoded, Bind.bind, Option.bind] at accepted; cases accepted
        | string text =>
            simp only [readObject?, decoded, Bind.bind, Option.bind] at accepted
            cases parsed : Binary.Text.parse text with
            | none => simp only [parsed] at accepted; cases accepted
            | some word =>
                simp only [parsed] at accepted
                cases read : Binary.canonicalDecodeWith codec word with
                | none => simp only [read] at accepted; cases accepted
                | some found =>
                    simp only [read] at accepted
                    split at accepted
                    · rename_i same
                      cases Option.some.inj accepted
                      exact same
                    · cases accepted
  · intro same
    rw [same]
    exact readObject?_nativeObject codec value

def requestTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) : Tower.Tm bound.length :=
  nativeObject GeneralPremiseReceiptWire.requestCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, claim)

def proofTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (proof : Proof) : Tower.Tm bound.length :=
  nativeObject GeneralPremiseReceiptWire.proofCodec (GeneralPremiseReceiptWire.header scope handler plan bound type, proof)

def readRequest? (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : Tower.Tm bound.length) : Option Claim := do
  let value ← readObject? GeneralPremiseReceiptWire.requestCodec native
  if headerEqual value.1 (GeneralPremiseReceiptWire.header scope handler plan bound type) then some value.2 else none

def readProof? (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : Tower.Tm bound.length) : Option Proof := do
  let value ← readObject? GeneralPremiseReceiptWire.proofCodec native
  if headerEqual value.1 (GeneralPremiseReceiptWire.header scope handler plan bound type) then some value.2 else none

theorem readRequest?_exact (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : Tower.Tm bound.length) (claim : Claim) :
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
    simp only [same, readRequest?, requestTerm, readObject?_nativeObject, Bind.bind, Option.bind]
    rw [(headerEqual_exact _ _).mpr rfl]
    rfl

theorem readProof?_exact (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (native : Tower.Tm bound.length) (proof : Proof) :
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
    simp only [same, readProof?, proofTerm, readObject?_nativeObject, Bind.bind, Option.bind]
    rw [(headerEqual_exact _ _).mpr rfl]
    rfl

/-- Independent original source meaning on the literal native request image. -/
def Meaning (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native : Tower.Tm bound.length) : Prop :=
  ∃ claim : Claim, native = requestTerm scope handler plan bound type claim ∧
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim

def target (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : AdmissionObject where
  Carrier := Tower.Tm bound.length
  Meaning := Meaning scope handler dynamic plan bound type

/-- Native evidence is actual declared data syntax. Its original receipt
meaning is independent of the implementation of the native reader/checker. -/
def guest (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : NativeProofSystem (Tower.Tm bound.length) where
  ProofObject := Tower.Tm bound.length
  Judges nativeProof native := ∃ (claim : Claim) (proof : Proof),
    native = requestTerm scope handler plan bound type claim ∧
    nativeProof = proofTerm scope handler plan bound type proof ∧
    proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2

def check (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr)
    (native nativeProof : Tower.Tm bound.length) : Bool :=
  match readRequest? scope handler plan bound type native,
      readProof? scope handler plan bound type nativeProof with
  | some claim, some proof => GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof
  | _, _ => false

theorem check_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : Tower.Tm bound.length) :
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
    (bound : List TypeExpr) (type : TypeExpr) (native : Tower.Tm bound.length) :
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
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : Tower.Tm bound.length) :
    SemanticServiceInvocation.Request (service scope handler dynamic plan bound type) := .nativeProof native nativeProof

theorem invocation_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (native nativeProof : Tower.Tm bound.length) :
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
    have checked : check scope handler dynamic plan bound type (requestTerm scope handler plan bound type claim)
        (proofTerm scope handler plan bound type proof) = true := by
      change (if check scope handler dynamic plan bound type _ _ then some _ else none) = some _ at accepted
      split at accepted
      · assumption
      · cases accepted
    rw [check_source] at checked
    exact ⟨proof, (GeneralPremiseNativeEvidence.check_exact dynamic plan bound type claim proof).mp checked⟩

/-- The actual native data signature forms both physical request objects.
This does not confuse data formation with original receipt validity. -/
theorem request_judgment (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation NativeWireData.rules context) :
    FormationSensitive.Judgment NativeWireData.rules context
      (requestTerm scope handler plan bound type claim) NativeWireData.dataType :=
  NativeWireData.encode_judgment formed _

theorem proof_judgment (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (proof : Proof) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation NativeWireData.rules context) :
    FormationSensitive.Judgment NativeWireData.rules context
      (proofTerm scope handler plan bound type proof) NativeWireData.dataType :=
  NativeWireData.encode_judgment formed _

open SemanticService

def requiredInterface (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) : Interface (target scope handler dynamic plan bound type) :=
  .nativeProof (guest scope handler dynamic plan bound type)

theorem service_interface_matches (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) :
    InterfaceMatches (RawService.erase (service scope handler dynamic plan bound type))
      (requiredInterface scope handler dynamic plan bound type) := .nativeProof _ _

def invokeRouted (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (requested : String)
    (native nativeProof : Tower.Tm bound.length) : Option (Tower.Tm bound.length) :=
  if requested = serviceHead then
    (SemanticServiceInvocation.invoke
      (invocation scope handler dynamic plan bound type native nativeProof)).acceptedValue
  else none

theorem routed_accepted_iff (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (requested : String)
    (native nativeProof output : Tower.Tm bound.length) :
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
    (native nativeProof : Tower.Tm bound.length) (wrong : requested ≠ serviceHead) :
    invokeRouted scope handler dynamic plan bound type requested native nativeProof = none := by
  change (if requested = serviceHead then
    (if check scope handler dynamic plan bound type native nativeProof then some native else none) else none) = none
  rw [if_neg wrong]

def callTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) : Tower.Tm bound.length :=
  NativeWireData.encode (callWire scope handler plan bound type claim proof)

def runCall? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (nativeCall : Tower.Tm bound.length) :
    Option (Tower.Tm bound.length) :=
  match NativeWireData.decode nativeCall with
  | some (.application requested [native, nativeProof]) =>
      if nativeCall = NativeWireData.encode (.application requested [native, nativeProof]) then
        invokeRouted scope handler dynamic plan bound type requested
          (NativeWireData.encode native) (NativeWireData.encode nativeProof)
      else none
  | _ => none

theorem runCall?_source (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof) :
    runCall? scope handler dynamic plan bound type (callTerm scope handler plan bound type claim proof) =
      some (requestTerm scope handler plan bound type claim) ↔
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  simp only [runCall?, callTerm, callWire, NativeWireData.decode_encode, ite_true]
  change invokeRouted scope handler dynamic plan bound type serviceHead
    (requestTerm scope handler plan bound type claim) (proofTerm scope handler plan bound type proof) =
      some (requestTerm scope handler plan bound type claim) ↔ _
  change (if check scope handler dynamic plan bound type _ _ then some _ else none) = some _ ↔ _
  rw [check_source, ← GeneralPremiseNativeEvidence.check_exact]
  cases GeneralPremiseNativeEvidence.check dynamic plan bound type claim proof <;> simp

/-- Actual native data formation is separate from checking its represented
source derivation. -/
theorem call_judgment (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (claim : Claim) (proof : Proof) {context : Tower.Ctx bound.length}
    (formed : FormationSensitive.ContextFormation NativeWireData.rules context) :
    FormationSensitive.Judgment NativeWireData.rules context
      (callTerm scope handler plan bound type claim proof) NativeWireData.dataType :=
  NativeWireData.encode_judgment formed _


/-- Accepted calls reflect the exact literal source request and the exact
original receipt, including all header and evidence bytes represented there. -/
theorem runCall?_exact (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (nativeCall output : Tower.Tm bound.length) :
    runCall? scope handler dynamic plan bound type nativeCall = some output ↔
      ∃ (claim : Claim) (proof : Proof),
        nativeCall = callTerm scope handler plan bound type claim proof ∧
        output = requestTerm scope handler plan bound type claim ∧
        proof.ValidWith dynamic plan bound type claim.1 ∧ proof.target = claim.2 := by
  constructor
  · intro accepted
    simp only [runCall?] at accepted
    split at accepted
    · rename_i requested native nativeProof decoded
      split at accepted
      · rename_i represented
        obtain ⟨role, outputAt, claim, proof, inputAt, proofAt, valid⟩ :=
          (routed_accepted_iff scope handler dynamic plan bound type requested
            (NativeWireData.encode native) (NativeWireData.encode nativeProof) output).mp accepted
        have requestWire : native = .string (Binary.Text.render
            (Binary.encodeWith GeneralPremiseReceiptWire.requestCodec
              (GeneralPremiseReceiptWire.header scope handler plan bound type, claim))) :=
          NativeWireData.encode_injective inputAt
        have proofWire : nativeProof = .string (Binary.Text.render
            (Binary.encodeWith GeneralPremiseReceiptWire.proofCodec
              (GeneralPremiseReceiptWire.header scope handler plan bound type, proof))) :=
          NativeWireData.encode_injective proofAt
        refine ⟨claim, proof, ?_, outputAt.symm.trans inputAt, valid⟩
        rw [role, requestWire, proofWire] at represented
        exact represented
      · cases accepted
    · cases accepted
  · rintro ⟨claim, proof, callAt, outputAt, valid⟩
    rw [callAt, outputAt]
    exact (runCall?_source scope handler dynamic plan bound type claim proof).mpr valid

/-- Unrestricted original finite receipt evidence has executable native
calls, and an accepted native call cannot invent an original source firing. -/
theorem source_iff_native_call (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) :
    GeneralPremiseNativeEvidence.Meaning dynamic plan bound type claim ↔ ∃ proof : Proof,
      runCall? scope handler dynamic plan bound type (callTerm scope handler plan bound type claim proof) =
        some (requestTerm scope handler plan bound type claim) := by
  constructor
  · rintro ⟨proof, valid⟩
    exact ⟨proof, (runCall?_source scope handler dynamic plan bound type claim proof).mpr valid⟩
  · rintro ⟨proof, accepted⟩
    exact ⟨proof, (runCall?_source scope handler dynamic plan bound type claim proof).mp accepted⟩

/-- The target checker and independent source checker agree at every exact
encoded source request and receipt. Native formation is a separate judgment. -/
theorem source_check_agrees (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (claim : Claim) (proof : Proof) :
    check scope handler dynamic plan bound type (requestTerm scope handler plan bound type claim)
      (proofTerm scope handler plan bound type proof) =
    Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.check scope handler dynamic plan bound type
      (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.requestTerm scope handler plan bound type claim)
      (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.proofTerm scope handler plan bound type proof) := by
  rw [check_source, Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.check_source]

namespace Discovery

/-- Input encoding adds only the optional native Data representation. -/
def inputTerm (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr)
    (type : TypeExpr) (query : Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.Discovery.Query) :
    Tower.Tm bound.length :=
  NativeWireData.encode
    (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.Discovery.callWire scope handler plan bound type query)

/-- The independent source operation performs discovery; this adapter only
checks its literal native Data boundary and attaches the actual returned wire. -/
def runCall? (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (input : Tower.Tm bound.length) :
    Option (Tower.Tm bound.length) := do
  let wire ← NativeWireData.decode input
  if input = NativeWireData.encode wire then
    let result ← Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.Discovery.runCall?
      scope handler dynamic plan bound type wire
    some (NativeWireData.encode result)
  else none

theorem runCall?_encode (scope handler : Lean.Name) (dynamic : DynamicProvider) (plan : Plan)
    (bound : List TypeExpr) (type : TypeExpr) (wire : CettaWire.Term) :
    runCall? scope handler dynamic plan bound type (NativeWireData.encode wire) =
      (Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.Discovery.runCall?
        scope handler dynamic plan bound type wire).map NativeWireData.encode := by
  simp only [runCall?, NativeWireData.decode_encode, Bind.bind, Option.bind, ite_true]
  cases Mettapedia.OSLF.MeTTaIL.AuthoredPremiseServices.Discovery.runCall?
    scope handler dynamic plan bound type wire <;> rfl

end Discovery

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseServices
