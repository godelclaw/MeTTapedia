import Mettapedia.GSLT.LanguageDef.SemanticServiceFamily
import Mettapedia.GSLT.LanguageDef.OperationCostProtocol
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.SnapshotBatch
import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GSLT.Distinction.OrderedAdministration

/-!
# Invocation of semantically qualified services

Requests retain the selected service and its actual face-specific input.
Decisions receive claims, native proof kernels receive claims and guest proof
objects, native operations receive raw source values, and external boundaries
receive claims and external certificates. The executable invocation never
converts one face into another or searches for missing evidence.

Source admission for an operation is a separate judgment, not an assumed
decision procedure on source meaning. Invocation can execute a raw operation
input; its result is semantically admitted only when that source premise is
available. The shared continuation theorem applies an existing admitted
operation to a successful result, retaining this precondition.

This is a typed invocation boundary. It neither parses external bytes nor
claims compilation/hosting adequacy or a step-for-step backend realization.

Formerly `Mettapedia.GSLT.LanguageDef.NIKServiceInvocation`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.GSLT.LanguageDef.NIKServiceInvocation`; it is now `Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.SemanticService

universe uArtifact uEvidence

variable {target : AdmissionObject.{uArtifact}}

/-- Each constructor carries only the input of its actual service face.
Proof objects have the guest's syntax; they need not yet judge the claim. -/
inductive Request : Service.{uArtifact, uEvidence} target →
    Type (max (uArtifact + 1) (uEvidence + 1)) where
  | directDecision {kernel : Checker.DecisionKernel target.Carrier target.Meaning}
      (claim : target.Carrier) : Request (.directDecision kernel)
  | nativeProof {guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier}
      {kernel : NativeProofKernel guest}
      {exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim)}
      (claim : target.Carrier) (proof : guest.ProofObject) :
      Request (.nativeProof guest kernel exactMeaning)
  | nativeOperation {source : AdmissionObject.{uArtifact}}
      {operation : source ⟶ target} (input : source.Carrier) :
      Request (.nativeOperation source operation)
  | certificateBoundary {Certificate : Type uEvidence}
      {checker : Checker target.Carrier Certificate}
      {authority : checker.Authority target.Meaning}
      (claim : target.Carrier) (certificate : Certificate) :
      Request (.certificateBoundary Certificate checker authority)

/-- The original request indexes every response, retaining its claim and
submitted proof/certificate. Rejection of evidence is not a negative decision. -/
inductive Response : {service : Service.{uArtifact, uEvidence} target} →
    Request service → Type (max (uArtifact + 1) (uEvidence + 1)) where
  | decided {kernel claim} (verdict : Bool) :
      Response (Request.directDecision (kernel := kernel) claim)
  | proofChecked {guest kernel exactMeaning claim proof} (accepted : Bool) :
      Response (Request.nativeProof (guest := guest) (kernel := kernel)
        (exactMeaning := exactMeaning) claim proof)
  | produced {source operation input} (value : target.Carrier) :
      Response (Request.nativeOperation (source := source) (operation := operation) input)
  | boundaryChecked {Certificate checker authority claim certificate} (accepted : Bool) :
      Response (Request.certificateBoundary (Certificate := Certificate)
        (checker := checker) (authority := authority) claim certificate)

/-- Only native operation execution needs a separately admitted source.
The other constructors introduce no extra source precondition. -/
inductive InputAdmission : {service : Service.{uArtifact, uEvidence} target} →
    Request service → Prop where
  | directDecision {kernel claim} :
      InputAdmission (Request.directDecision (kernel := kernel) claim)
  | nativeProof {guest kernel exactMeaning claim proof} :
      InputAdmission (Request.nativeProof (guest := guest) (kernel := kernel)
        (exactMeaning := exactMeaning) claim proof)
  | nativeOperation {source operation input} (meaningful : source.Meaning input) :
      InputAdmission (Request.nativeOperation (source := source) (operation := operation) input)
  | certificateBoundary {Certificate checker authority claim certificate} :
      InputAdmission (Request.certificateBoundary (Certificate := Certificate)
        (checker := checker) (authority := authority) claim certificate)

/-- Execute the supplied kernel/checker or the actual admitted arrow's raw
function. No semantic source judgment is decided by this function. -/
def invoke {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) : Response request := by
  cases request with
  | @directDecision kernel claim => exact .decided (kernel.decide claim)
  | @nativeProof guest kernel exactMeaning claim proof =>
      exact .proofChecked (kernel.decide claim proof)
  | @nativeOperation source operation input => exact .produced (operation.run input)
  | @certificateBoundary Certificate checker authority claim certificate =>
      exact .boundaryChecked (checker.check claim certificate)

/-- The value usable by a success-only continuation. For the three checking
faces this is exactly the submitted claim, never a substituted target. -/
def Response.acceptedValue {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request) : Option target.Carrier := by
  cases response with
  | @decided kernel claim verdict => exact if verdict then some claim else none
  | @proofChecked guest kernel exactMeaning claim proof accepted =>
      exact if accepted then some claim else none
  | @produced source operation input value => exact some value
  | @boundaryChecked Certificate checker authority claim certificate accepted =>
      exact if accepted then some claim else none

theorem direct_decision_true_iff
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning)
    (claim : target.Carrier) :
    invoke (Request.directDecision (kernel := kernel) claim) = .decided true ↔
      target.Meaning claim := by
  simpa [invoke] using kernel.correct claim

/-- Unlike evidence rejection, a negative direct decision refutes meaning. -/
theorem direct_decision_false_iff
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning)
    (claim : target.Carrier) :
    invoke (Request.directDecision (kernel := kernel) claim) = .decided false ↔
      ¬ target.Meaning claim := by
  rw [← kernel.correct]
  cases verdict : kernel.decide claim <;> simp [invoke, verdict]

theorem native_proof_checked_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) :
    invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning) claim proof) =
        .proofChecked true ↔ guest.Judges proof claim := by
  simpa [invoke] using kernel.correct claim proof

/-- The failed native object does not judge this claim. The theorem does
not say that the guest's entire proof fibre is empty. -/
theorem native_proof_rejected_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) :
    invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning) claim proof) =
        .proofChecked false ↔ ¬ guest.Judges proof claim := by
  rw [← kernel.correct]
  cases verdict : kernel.decide claim proof <;> simp [invoke, verdict]

theorem boundary_checked_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) :
    invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate) = .boundaryChecked true ↔ checker.check claim certificate = true := by
  simp [invoke]

theorem boundary_rejected_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) :
    invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate) = .boundaryChecked false ↔ checker.check claim certificate = false := by
  simp [invoke]

/-- Acceptance retains the submitted native claim as well as checking its
submitted proof. No other target claim can be returned by this crossing. -/
theorem native_proof_value_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) (value : target.Carrier) :
    (invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning)
      claim proof)).acceptedValue = some value ↔
      kernel.decide claim proof = true ∧ value = claim := by
  cases verdict : kernel.decide claim proof <;>
    simp [invoke, Response.acceptedValue, verdict, eq_comm]

/-- The corresponding target binding for a genuinely external certificate. -/
theorem boundary_value_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) (value : target.Carrier) :
    (invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate)).acceptedValue = some value ↔
      checker.check claim certificate = true ∧ value = claim := by
  cases verdict : checker.check claim certificate <;>
    simp [invoke, Response.acceptedValue, verdict, eq_comm]

theorem native_operation_produces
    {source : AdmissionObject.{uArtifact}} (operation : source ⟶ target)
    (input : source.Carrier) :
    invoke (Request.nativeOperation (operation := operation) input) =
      .produced (operation.run input) := rfl

theorem native_operation_input_admission_iff
    {source : AdmissionObject.{uArtifact}} (operation : source ⟶ target)
    (input : source.Carrier) :
    InputAdmission (Request.nativeOperation (operation := operation) input) ↔
      source.Meaning input := by
  constructor
  · intro admitted
    cases admitted with
    | nativeOperation meaningful => exact meaningful
  · exact InputAdmission.nativeOperation

/-- Every successful actual invocation supplies target meaning, using the
operation face's real source premise and the other faces' existing kernels. -/
theorem accepted_meaning {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) (admitted : InputAdmission request)
    {value : target.Carrier} (accepted : (invoke request).acceptedValue = some value) :
    target.Meaning value := by
  cases request with
  | @directDecision kernel claim =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact (kernel.correct claim).mp ‹kernel.decide claim = true›
      · cases accepted
  | @nativeProof guest kernel exactMeaning claim proof =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact (exactMeaning claim).mpr
          ⟨⟨proof, (kernel.correct claim proof).mp ‹kernel.decide claim proof = true›⟩⟩
      · cases accepted
  | @nativeOperation source operation input =>
      cases admitted with
      | nativeOperation meaningful =>
          obtain rfl := Option.some.inj accepted
          exact operation.preserves input meaningful
  | @certificateBoundary Certificate checker authority claim certificate =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact authority.sound claim certificate ‹checker.check claim certificate = true›
      · cases accepted

/-- Execute an already admitted continuation on the actual returned value.
The original indexed response is not rewritten or recoded as a certificate. -/
def continueWith {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request) : Option later.Carrier :=
  response.acceptedValue.map operation.run

theorem continuation_preserves {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) (admitted : InputAdmission request)
    {output : later.Carrier} (returned : continueWith operation (invoke request) = some output) :
    later.Meaning output := by
  obtain ⟨value, accepted, rfl⟩ := Option.map_eq_some_iff.mp returned
  exact operation.preserves value (accepted_meaning request admitted accepted)

/-- Rejected replies do not silently run a success continuation. -/
theorem no_continuation_of_no_value {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request)
    (rejected : response.acceptedValue = none) : continueWith operation response = none := by
  simp [continueWith, rejected]

/-! ## Four actual inputs, one nonidentity continuation, and failed evidence -/

namespace PositiveNaturalControl

open AdmissionCanary

/-- The native guest's positive-number introduction proof syntax. -/
inductive Proof where
  | successor (predecessor : Nat)

def guest : NativeProofSystem.{0, 0} Nat where
  ProofObject := Proof
  Judges proof claim := match proof with
    | .successor predecessor => claim = predecessor + 1

/-- This kernel checks the submitted introduction and its claimed result;
it does not synthesize a proof from the claim. -/
def kernel : NativeProofKernel guest where
  decide claim proof := match proof with
    | .successor predecessor => decide (claim = predecessor + 1)
  correct claim proof := by cases proof; simp [guest]

theorem guest_exact (claim : Nat) :
    positiveNaturals.Meaning claim ↔ Nonempty (guest.ProofFibre claim) := by
  constructor
  · intro meaningful
    obtain ⟨predecessor, equal⟩ := Nat.exists_eq_succ_of_ne_zero meaningful
    exact ⟨⟨.successor predecessor, equal⟩⟩
  · rintro ⟨⟨proof, judged⟩⟩
    cases proof with
    | successor predecessor =>
        change claim = predecessor + 1 at judged
        change claim ≠ 0
        omega

def proofService : Service.{0, 0} positiveNaturals :=
  .nativeProof guest kernel guest_exact

/-- A different, external evidence language: finite Boolean words witness
a positive number by their length. Their symbols remain boundary evidence. -/
def wordChecker : Checker Nat (List Bool) where
  check claim certificate := decide (claim = certificate.length + 1)

theorem wordAuthority : wordChecker.Authority positiveNaturals.Meaning where
  sound claim certificate accepted := by
    have equal : claim = certificate.length + 1 := by simpa [wordChecker] using accepted
    change claim ≠ 0
    omega
  complete claim meaningful := by
    obtain ⟨predecessor, equal⟩ := Nat.exists_eq_succ_of_ne_zero meaningful
    exact ⟨List.replicate predecessor false, by simp [wordChecker, equal]⟩

def boundaryService : Service.{0, 0} positiveNaturals :=
  .certificateBoundary (List Bool) wordChecker wordAuthority

def decisionRequest : Request (SemanticService.Canary.direct : Service.{0, 0} positiveNaturals) :=
  .directDecision (2 : Nat)

def proofRequest : Request proofService := .nativeProof (2 : Nat) (Proof.successor 1)

def operationRequest : Request (SemanticService.Canary.native : Service.{0, 0} positiveNaturals) :=
  .nativeOperation (1 : Nat)

def boundaryRequest : Request boundaryService := .certificateBoundary (2 : Nat) [false]

/-- Every face really executes its own input and returns the common value
two. The native operation starts from one, not from a submitted target claim. -/
theorem four_invocations :
    invoke decisionRequest = .decided true ∧
      invoke proofRequest = .proofChecked true ∧
      invoke operationRequest = .produced (2 : Nat) ∧
      invoke boundaryRequest = .boundaryChecked true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The existing nonidentity admitted successor continues all four actual
crossings. Semantic admission is obtained through the common theorem. -/
theorem four_continuations :
    continueWith successor (invoke decisionRequest) = some (3 : Nat) ∧
      continueWith successor (invoke proofRequest) = some (3 : Nat) ∧
      continueWith successor (invoke operationRequest) = some (3 : Nat) ∧
      continueWith successor (invoke boundaryRequest) = some (3 : Nat) ∧
      positiveNaturals.Meaning (3 : Nat) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact continuation_preserves successor operationRequest
    (.nativeOperation (Nat.succ_ne_zero 0)) rfl

/-- The claim is meaningful and has an accepted native proof, yet a
different submitted proof is rejected and cannot run the continuation. -/
theorem bad_native_proof_does_not_refute :
    positiveNaturals.Meaning (2 : Nat) ∧
      invoke proofRequest = .proofChecked true ∧
      invoke (Request.nativeProof (target := positiveNaturals)
        (kernel := kernel) (exactMeaning := guest_exact)
        (2 : Nat) (Proof.successor 0)) = .proofChecked false ∧
      continueWith successor
        (invoke (Request.nativeProof (target := positiveNaturals)
          (kernel := kernel) (exactMeaning := guest_exact)
          (2 : Nat) (Proof.successor 0))) = none := by
  exact ⟨Nat.succ_ne_zero 1, rfl, rfl, rfl⟩

/-- Rejection of an external certificate likewise does not negate its
claim, even though accepted certificates are semantically authoritative. -/
theorem bad_certificate_does_not_refute :
    positiveNaturals.Meaning (2 : Nat) ∧
      invoke boundaryRequest = .boundaryChecked true ∧
      invoke (Request.certificateBoundary (target := positiveNaturals)
        (checker := wordChecker) (authority := wordAuthority) (2 : Nat) []) = .boundaryChecked false ∧
      continueWith successor
        (invoke (Request.certificateBoundary (target := positiveNaturals)
          (checker := wordChecker) (authority := wordAuthority) (2 : Nat) [])) = none := by
  exact ⟨Nat.succ_ne_zero 1, rfl, rfl, rfl⟩

/-- Changing only the submitted claim rejects both of these previously
accepted evidence objects; the changed claim is still a meaningful number. -/
theorem altered_claim_rejected :
    positiveNaturals.Meaning (3 : Nat) ∧
      invoke (Request.nativeProof (target := positiveNaturals)
        (kernel := kernel) (exactMeaning := guest_exact)
        (3 : Nat) (Proof.successor 1)) = .proofChecked false ∧
      invoke (Request.certificateBoundary (target := positiveNaturals)
        (checker := wordChecker) (authority := wordAuthority) (3 : Nat) [false]) =
        .boundaryChecked false := by
  exact ⟨Nat.succ_ne_zero 2, rfl, rfl⟩

/-- Zero is a genuinely false direct decision, a different outcome from
rejected evidence for the meaningful claims above. -/
theorem false_decision_refutes :
    invoke (Request.directDecision.{0, 0} (target := positiveNaturals)
      (kernel := SemanticService.Canary.nonzeroDecision) (0 : Nat)) =
        .decided false ∧ ¬ positiveNaturals.Meaning (0 : Nat) := by
  exact ⟨rfl, (direct_decision_false_iff.{0, 0} (target := positiveNaturals)
    SemanticService.Canary.nonzeroDecision (0 : Nat)).mp rfl⟩

/-- The admitted range of successor is a proper subset of target meaning:
one is meaningful but no meaningful source input produces it. -/
theorem native_admitted_range_is_proper :
    positiveNaturals.Meaning (1 : Nat) ∧
      ¬ ∃ request : Request (SemanticService.Canary.native : Service.{0, 0} positiveNaturals),
        InputAdmission request ∧ (invoke request).acceptedValue = some (1 : Nat) := by
  refine ⟨Nat.succ_ne_zero 0, ?_⟩
  rintro ⟨request, admitted, returned⟩
  cases request with
  | nativeOperation input =>
      cases admitted with
      | nativeOperation meaningful =>
          have equal : Nat.succ input = (1 : Nat) := Option.some.inj returned
          exact meaningful (Nat.succ.inj equal)

/-- A nonidentity operation whose source premise really matters for raw
execution: doubling a non-admitted zero returns non-admitted zero. -/
def doubling : positiveNaturals ⟶ positiveNaturals where
  run (value : Nat) := value + value
  preserves value meaningful := by
    intro zero
    exact meaningful (Nat.add_eq_zero_iff.mp zero).1

theorem raw_operation_is_not_source_admission :
    invoke (Request.nativeOperation (operation := doubling) (0 : Nat)) = .produced (0 : Nat) ∧
      ¬ InputAdmission (Request.nativeOperation (operation := doubling) (0 : Nat)) ∧
      ¬ positiveNaturals.Meaning (0 : Nat) := by
  refine ⟨rfl, ?_, fun meaningful => meaningful rfl⟩
  intro admitted
  exact ((native_operation_input_admission_iff doubling (0 : Nat)).mp admitted) rfl

end PositiveNaturalControl

#print axioms direct_decision_true_iff
#print axioms direct_decision_false_iff
#print axioms native_proof_checked_iff
#print axioms native_proof_rejected_iff
#print axioms boundary_checked_iff
#print axioms boundary_rejected_iff
#print axioms native_proof_value_iff
#print axioms boundary_value_iff
#print axioms native_operation_input_admission_iff
#print axioms accepted_meaning
#print axioms continuation_preserves
#print axioms no_continuation_of_no_value
#print axioms PositiveNaturalControl.guest_exact
#print axioms PositiveNaturalControl.wordAuthority
#print axioms PositiveNaturalControl.four_invocations
#print axioms PositiveNaturalControl.four_continuations
#print axioms PositiveNaturalControl.bad_native_proof_does_not_refute
#print axioms PositiveNaturalControl.bad_certificate_does_not_refute
#print axioms PositiveNaturalControl.altered_claim_rejected
#print axioms PositiveNaturalControl.false_decision_refutes
#print axioms PositiveNaturalControl.native_admitted_range_is_proper
#print axioms PositiveNaturalControl.raw_operation_is_not_source_admission

/-! ## Conditional reports and current reliance

The checked service faces above retain their soundness obligations. An
entrusted report is a different carrier: it retains named assumptions and a
conditional consequence, never an inhabitant of a checked authority's evidence.
-/

namespace Reliance

open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed

structure Scope (Principal Task Context Epoch : Type) where
  principal : Principal
  task : Task
  context : Context
  epoch : Epoch
  deriving DecidableEq

structure Premise (Principal Task Context Epoch Occurrence Claim : Type) where
  scope : Scope Principal Task Context Epoch
  occurrence : Occurrence
  claim : Claim
  deriving DecidableEq

variable {Dependency : Type} [DecidableEq Dependency]
variable (meaning : Dependency → Prop)

/-- A data result with an explicit conditional interpretation. The implication
is checked mathematics; the named premises are not asserted to be true. -/
structure Conditional (target : AdmissionObject.{0}) where
  value : target.Carrier
  dependencies : Finset Dependency
  conditional : (∀ dependency ∈ dependencies, meaning dependency) → target.Meaning value

namespace Conditional

variable {meaning} {source middle later : AdmissionObject.{0}}

def checked {service : Service.{0, 0} source} (request : Request service)
    (admitted : InputAdmission request) (value : source.Carrier)
    (accepted : (invoke request).acceptedValue = some value) : Conditional meaning source :=
  ⟨value, ∅, fun _ => accepted_meaning request admitted accepted⟩

def map (operation : source ⟶ later) (result : Conditional meaning source) : Conditional meaning later :=
  ⟨operation.run result.value, result.dependencies,
    fun supplied => operation.preserves _ (result.conditional supplied)⟩

def require (prior : Finset Dependency) (result : Conditional meaning source) : Conditional meaning source :=
  ⟨result.value, prior ∪ result.dependencies, fun supplied =>
    result.conditional (fun dependency member => supplied dependency (Finset.mem_union_right _ member))⟩

/-- The selected continuation is executed on the actual result data. Every
previous premise remains in the combined dependency set. -/
def bind (result : Conditional meaning source)
    (next : source.Carrier → Conditional meaning later) : Conditional meaning later :=
  (next result.value).require result.dependencies

def product (first second : AdmissionObject.{0}) : AdmissionObject.{0} :=
  ⟨first.Carrier × second.Carrier, fun value => first.Meaning value.1 ∧ second.Meaning value.2⟩

def pair (first : Conditional meaning source) (second : Conditional meaning later) :
    Conditional meaning (product source later) :=
  ⟨(first.value, second.value), first.dependencies ∪ second.dependencies, fun supplied =>
    ⟨first.conditional (fun dependency member => supplied dependency (Finset.mem_union_left _ member)),
      second.conditional (fun dependency member => supplied dependency (Finset.mem_union_right _ member))⟩⟩

theorem bind_keeps_each_premise (result : Conditional meaning source)
    (next : source.Carrier → Conditional meaning later) :
    result.dependencies ⊆ (result.bind next).dependencies ∧
      (next result.value).dependencies ⊆ (result.bind next).dependencies :=
  ⟨Finset.subset_union_left, Finset.subset_union_right⟩

omit [DecidableEq Dependency] in
theorem map_comp (first : source ⟶ middle) (second : middle ⟶ later)
    (result : Conditional meaning source) :
    (result.map first).map second = result.map (first ≫ second) := by
  cases result
  rfl

theorem bind_assoc (result : Conditional meaning source)
    (next : source.Carrier → Conditional meaning middle)
    (last : middle.Carrier → Conditional meaning later) :
    (result.bind next).bind last = result.bind (fun value => (next value).bind last) := by
  cases result
  simp only [bind, require, Finset.union_assoc]

/-- The loose interpretation retains the exact assumption interface. Its
witness is a conditional implication, not checked evidence for the value. -/
def interpretation (target : AdmissionObject.{0}) :
    Mettapedia.GSLT.LooseRelationEquipment.Loose (Finset Dependency) target.Carrier :=
  fun dependencies value => PLift ((∀ dependency ∈ dependencies, meaning dependency) → target.Meaning value)

def asInterpretation (result : Conditional meaning source) :
    interpretation (meaning := meaning) source result.dependencies result.value := ⟨result.conditional⟩

/-- An existing admitted semantic operation gives the actual nonidentity
right boundary of a loose square. No evidence is obtained by forgetting its
left assumption boundary. -/
def interpretationCell (operation : source ⟶ later) :
    Mettapedia.GSLT.LooseRelationEquipment.Cell id operation.run
      (interpretation (meaning := meaning) source) (interpretation (meaning := meaning) later) where
  map witness := ⟨fun supplied => operation.preserves _ (witness.down supplied)⟩

def requireCell (prior : Finset Dependency) :
    Mettapedia.GSLT.LooseRelationEquipment.Cell (fun dependencies => prior ∪ dependencies) id
      (interpretation (meaning := meaning) source) (interpretation (meaning := meaning) source) where
  map witness := ⟨fun supplied => witness.down (fun dependency member =>
    supplied dependency (Finset.mem_union_right _ member))⟩

omit [DecidableEq Dependency] in
theorem interpretation_cells_compose (first : source ⟶ middle) (second : middle ⟶ later) :
    Mettapedia.GSLT.LooseRelationEquipment.Cell.vcomp (interpretationCell (meaning := meaning) first) (interpretationCell (meaning := meaning) second) =
      interpretationCell (meaning := meaning) (first ≫ second) := by
  ext dependencies value witness
  rfl

end Conditional

/-- Trusting one report introduces exactly its named premise, rather than
calling any of the checked service constructors. -/
def report {Principal Task Context Epoch Occurrence : Type}
    [DecidableEq Principal] [DecidableEq Task] [DecidableEq Context]
    [DecidableEq Epoch] [DecidableEq Occurrence]
    (target : AdmissionObject.{0}) [DecidableEq target.Carrier]
    (premise : Premise Principal Task Context Epoch Occurrence target.Carrier) :
    Conditional (fun dependency : Premise Principal Task Context Epoch Occurrence target.Carrier =>
      target.Meaning dependency.claim) target :=
  ⟨premise.claim, {premise}, fun supplied => supplied premise (Finset.mem_singleton_self _)⟩

section Adoption

variable {Provider Resource Authority : Type}
variable [DecidableEq Provider] [DecidableEq Resource]
variable [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
variable {target : AdmissionObject.{0}}

/-- Acceptance licenses a new use of the data under current policy. It does
not prove the premises or convert the report into checked semantic evidence. -/
def adopt (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (result : Conditional meaning target) :
    Except (Conditional meaning target) (Conditional meaning target) :=
  if requirement.handle = current.handle ∧ FrameUpdate current.available requirement.required then
    if ∀ dependency ∈ result.dependencies, active dependency = true then .ok result else .error result
  else .error result

omit [DecidableEq Dependency] in
theorem adopt_admitted (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (result adopted : Conditional meaning target)
    (accepted : adopt meaning requirement current active result = .ok adopted) :
    requirement.Current current ∧ (∀ dependency ∈ result.dependencies, active dependency = true) ∧ adopted = result := by
  unfold adopt at accepted
  split at accepted
  · rename_i granted
    split at accepted
    · rename_i currentDependencies
      exact ⟨granted, currentDependencies,
        (Except.ok.inj accepted).symm⟩
    · cases accepted
  · cases accepted

omit [DecidableEq Dependency] in
/-- A refusal retains the exact report. Old premises are never rewritten to
the new epoch or erased by the policy decision. -/
theorem adopt_refused_retains (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (result refused : Conditional meaning target)
    (rejected : adopt meaning requirement current active result = .error refused) : refused = result := by
  unfold adopt at rejected
  split at rejected
  · split at rejected
    · cases rejected
    · exact (Except.error.inj rejected).symm
  · exact (Except.error.inj rejected).symm

def publish (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (history : List (Conditional meaning target))
    (result : Conditional meaning target) :
    List (Conditional meaning target) × Except (Conditional meaning target) (Conditional meaning target) :=
  match adopt meaning requirement current active result with
  | .ok admitted => (history ++ [admitted], .ok admitted)
  | .error retained => (history, .error retained)

omit [DecidableEq Dependency] in
theorem publication_keeps_historical_dependencies
    (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (history : List (Conditional meaning target))
    (result : Conditional meaning target) :
    history <+: (publish meaning requirement current active history result).1 := by
  unfold publish
  split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- Both adoption outcomes retain their original conditional packet. -/
def original {meaning : Dependency → Prop} (outcome : Except (Conditional meaning target) (Conditional meaning target)) : Conditional meaning target :=
  match outcome with
  | .ok result | .error result => result

omit [DecidableEq Dependency] in
theorem adoption_returns_original
    (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)]
    (active : Dependency → Bool) (result : Conditional meaning target) :
    original (adopt meaning requirement current active result) = result := by
  cases issued : adopt meaning requirement current active result with
  | ok accepted => exact (adopt_admitted meaning requirement current active result accepted issued).2.2
  | error retained => exact adopt_refused_retains meaning requirement current active result retained issued

abbrev Review := Sum (Conditional meaning target) (Except (Conditional meaning target) (Conditional meaning target))

def reviewStable : Review (target := target) meaning → Bool
  | .inl _ => false
  | .inr _ => true

def reviewRead : Review (target := target) meaning → Conditional meaning target
  | .inl pending => pending
  | .inr outcome => original outcome

/-- One actual adoption boundary, embedded in the existing administration
interface. Refusal remains an observable retained result, rather than an
empty successor list. This supplies no scheduling or physical-cost bound. -/
def reviewSystem (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)] (active : Dependency → Bool) :
    Mettapedia.GSLT.Distinction.OrderedSystem (Review (target := target) meaning) where
  step
    | .inl pending => [.inr (adopt meaning requirement current active pending)]
    | .inr _ => []
  halted := reviewStable meaning

omit [DecidableEq Dependency] in
theorem review_preserves_assumption_packet
    (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)] (active : Dependency → Bool) :
    (reviewSystem (target := target) meaning requirement current active).AdministrationPreserves (reviewStable meaning) (reviewRead meaning) := by
  intro state administrative next member
  cases state with
  | inl pending =>
      have same := List.mem_singleton.mp member
      cases same
      exact adoption_returns_original meaning requirement current active pending
  | inr _ => cases administrative

/-- A deliberately lossy consumer discards refused branches. This is used
only to expose its missing erasure licence. -/
def discardRefused (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)] (active : Dependency → Bool) :
    Mettapedia.GSLT.Distinction.OrderedSystem (Review (target := target) meaning) where
  step
    | .inl pending => match adopt meaning requirement current active pending with
        | .ok accepted => [.inr (.ok accepted)]
        | .error _ => []
    | .inr _ => []
  halted := reviewStable meaning

omit [DecidableEq Dependency] in
theorem refusal_does_not_license_erasing_named_assumptions
    (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (current : CheckedGrant.View Provider Resource Authority)
    [Decidable (FrameUpdate current.available requirement.required)] (active : Dependency → Bool)
    (result : Conditional meaning target)
    (refused : adopt meaning requirement current active result = .error result)
    (outstanding : result.dependencies ≠ ∅) :
    ¬ (discardRefused (target := target) meaning requirement current active).ErasurePreserves (reviewStable meaning)
      (fun state => (reviewRead meaning state).dependencies) (fun _ => ∅) := by
  intro licensed
  apply outstanding
  simpa only [reviewRead] using licensed (.inl result) rfl (by simp only [discardRefused, refused])

end Adoption

/-! ## Dependencies around the actual retained primitive provider -/

namespace Tracked

open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

variable {Op State Fault Answer : Type} {Reply : Op → Type}
variable (step : State → (operation : Op) → State × Except Fault (Reply operation))
variable (used : State → (operation : Op) → Except Fault (Reply operation) → Finset Dependency)

def handle (state : State × Finset Dependency) (operation : Op) :
    (State × Finset Dependency) × Except Fault (Reply operation) :=
  let response := step state.1 operation
  ((response.1, state.2 ∪ used state.1 operation response.2), response.2)

abbrev provider := PrimitiveProgram.provider (handle step used)
abbrev client (Answer : Type) := PrimitiveProgram.client Op Reply Answer Fault
abbrev Saved (Answer : Type) := Nat × Outcome (provider step used) (client Answer) PUnit.unit

/-- The decoration preserves the actual reply and the entire provider state,
so values, faults, effects, occurrence IDs and residual control remain intact. -/
def projection : Hom (provider step used) (PrimitiveProgram.provider step) where
  map state := state.1
  step _ _ := rfl

def addPrior (prior : Finset Dependency) : Hom (provider step used) (provider step used) where
  map state := (state.1, prior ∪ state.2)
  step state operation := by simp only [provider, PrimitiveProgram.provider, handle, Finset.union_assoc]

def slice (cost : State → Op → Nat) (allowance : Nat) (program : Prog Op Reply Answer)
    (state : State) (dependencies : Finset Dependency) : Saved step used Answer :=
  Mettapedia.Machines.Cursor.advance (provider step used) (client Answer)
    (fun current operation => cost current.1 operation) allowance ⟨PUnit.unit, .ok program, state, dependencies⟩

theorem projected_slice_account (cost : State → Op → Nat) (allowance : Nat)
    (program : Prog Op Reply Answer) (state : State) (dependencies : Finset Dependency) :
    ((slice step used cost allowance program state dependencies).1,
      (projection step used).outcome (client Answer) (slice step used cost allowance program state dependencies).2) =
      Mettapedia.Machines.Cursor.advance (PrimitiveProgram.provider step) (client Answer)
        (PrimitiveProgram.charge cost step) allowance ⟨PUnit.unit, .ok program, state⟩ :=
  (projection step used).advance_account (client Answer)
    (fun current operation => cost current.1 operation) (PrimitiveProgram.charge cost step)
    (fun _ _ => rfl) allowance ⟨PUnit.unit, .ok program, state, dependencies⟩

theorem projected_resume_account (cost : State → Op → Nat) (allowance : Nat) (saved : Saved step used Answer) :
    ((Mettapedia.Machines.Cursor.resume (provider step used) (client Answer)
        (fun current operation => cost current.1 operation) allowance saved).1,
      (projection step used).outcome (client Answer)
        (Mettapedia.Machines.Cursor.resume (provider step used) (client Answer)
          (fun current operation => cost current.1 operation) allowance saved).2) =
      Mettapedia.Machines.Cursor.resume (PrimitiveProgram.provider step) (client Answer) (PrimitiveProgram.charge cost step)
        allowance (saved.1, (projection step used).outcome (client Answer) saved.2) :=
  (projection step used).resume_account (client Answer)
    (fun current operation => cost current.1 operation) (PrimitiveProgram.charge cost step)
    (fun _ _ => rfl) allowance saved

/-- Prefix assumptions are propagated by a constructed provider map. This
law applies to every dependent continuation, including a bound program. -/
theorem prefix_slice (cost : State → Op → Nat) (allowance : Nat)
    (program : Prog Op Reply Answer) (state : State) (dependencies prior : Finset Dependency) :
    ((slice step used cost allowance program state dependencies).1,
      (addPrior step used prior).outcome (client Answer) (slice step used cost allowance program state dependencies).2) =
      slice step used cost allowance program state (prior ∪ dependencies) :=
  (addPrior step used prior).advance_account (client Answer)
    (fun current operation => cost current.1 operation) (fun current operation => cost current.1 operation)
    (fun _ _ => rfl) allowance ⟨PUnit.unit, .ok program, state, dependencies⟩

variable {Owner : Type} [DecidableEq Owner]

/-- The existing independent-owner batch resumes complete retained accounts.
It does not project jobs to answers before preparing or joining them. -/
def parallelKernel (cost : State → Op → Nat) :
    Mettapedia.Machines.SnapshotBatch.Kernel Unit (Owner × Nat) Unit Owner (Saved step used Answer) :=
  Mettapedia.Machines.SnapshotBatch.Kernel.fromOwnerAction fun _ allowance saved =>
    Mettapedia.Machines.Cursor.resume (provider step used) (client Answer)
      (fun current operation => cost current.1 operation) allowance saved

theorem parallel_is_serial_on_independent_owners (cost : State → Op → Nat)
    (jobs : Owner → Saved step used Answer) (requests : List (Owner × Nat))
    (independent : (requests.map Prod.fst).Nodup) :
    (parallelKernel step used cost).batch () (fun _ => ()) jobs requests =
      (parallelKernel step used cost).run () (fun _ => ()) jobs requests :=
  (parallelKernel step used cost).batch_eq_run () (fun _ => ()) jobs requests independent

end Tracked

namespace Reported

variable {Op State Fault : Type}

/-- This specialization derives the annotation from the actual conditional
reply. It cannot silently replace the reply's named premises with a basis tag. -/
def dependencies (targets : Op → AdmissionObject.{0}) (_state : State) (operation : Op) :
    Except Fault (Conditional meaning (targets operation)) → Finset Dependency
  | .ok report => report.dependencies
  | .error _ => ∅

theorem successful_reply_is_recorded (targets : Op → AdmissionObject.{0})
    (handler : State → (operation : Op) → State × Except Fault (Conditional meaning (targets operation)))
    (state next : State) (prior : Finset Dependency) (operation : Op)
    (report : Conditional meaning (targets operation))
    (returned : handler state operation = (next, .ok report)) :
    Tracked.handle handler (dependencies meaning targets) (state, prior) operation =
      ((next, prior ∪ report.dependencies), .ok report) := by
  simp only [Tracked.handle, returned, dependencies]

end Reported

namespace Controls

open AdmissionCanary
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.Cursor

abbrev Fact := Premise Nat Nat Nat Nat Nat Nat
local instance : DecidableEq Fact := inferInstanceAs (DecidableEq (Premise Nat Nat Nat Nat Nat Nat))
local instance : DecidableEq positiveNaturals.Carrier := inferInstanceAs (DecidableEq Nat)
def premiseMeaning (fact : Fact) := positiveNaturals.Meaning fact.claim
def first : Fact := ⟨⟨7, 9, 11, 3⟩, 10, 2⟩
def second : Fact := ⟨⟨7, 9, 11, 3⟩, 11, 4⟩
def falseReport : Fact := ⟨⟨7, 9, 11, 3⟩, 12, 0⟩

def sumPositive : Conditional.product positiveNaturals positiveNaturals ⟶ positiveNaturals where
  run pair := Nat.add pair.1 pair.2
  preserves := by
    intro pair positive
    change Nat.add pair.1 pair.2 ≠ Nat.zero
    exact Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero positive.1) pair.2)

def conditionalResult : Conditional premiseMeaning positiveNaturals :=
  ((report positiveNaturals first).pair (report positiveNaturals second)).map sumPositive

inductive Op where
  | ask (fact : Fact)
  | emit (value : Nat)
  | fail (code : Nat)

def Reply : Op → Type
  | .ask _ => Nat
  | .emit _ | .fail _ => Unit

abbrev State := Nat × List (Nat × Nat)

def step (state : State) (operation : Op) : State × Except Nat (Reply operation) :=
  match operation with
  | .ask fact => ((state.1 + 1, state.2 ++ [(state.1, fact.occurrence)]), .ok fact.claim)
  | .emit value => ((state.1 + 1, state.2 ++ [(state.1, 1000 + value)]), .ok ())
  | .fail code => ((state.1 + 1, state.2 ++ [(state.1, 2000 + code)]), .error code)

def used (_state : State) (operation : Op) (_reply : Except Nat (Reply operation)) : Finset Fact :=
  match operation with
  | .ask fact => {fact}
  | .emit _ | .fail _ => ∅

def cost (_state : State) (_operation : Op) : Nat := 1
def firstCall : Prog Op Reply Nat := .call (.ask first) .ret
def next (value : Nat) : Prog Op Reply Nat :=
  .call (.emit value) fun _ => .call (.ask second) fun other => .ret (Nat.add value other)
def program := firstCall.bind next
def faultProgram : Prog Op Reply Nat :=
  .call (.ask first) fun value => .call (.emit value) fun _ => .call (.fail 99) fun _ => .ret 0

abbrev Saved := Tracked.Saved step used Nat
def cut : Saved := Tracked.slice step used cost 1 program (0, []) ∅
def completed : Saved := Tracked.slice step used cost 4 program (0, []) ∅
def faultCut : Saved := Tracked.slice step used cost 1 faultProgram (0, []) ∅
def faulted : Saved := Tracked.slice step used cost 4 faultProgram (0, []) ∅

structure View where
  paid : Nat
  status : Nat
  answer : Option Nat
  fault : Option Nat
  history : List (Nat × Nat)
  dependencies : Finset Fact
  deriving DecidableEq

def view (saved : Saved) : View :=
  let actual := PrimitiveProgram.readOutcome (Tracked.handle step used) saved.2
  match actual.1 with
  | .inl (.ok answer) => ⟨saved.1, 0, some answer, none, actual.2.1.2, actual.2.2⟩
  | .inl (.error fault) => ⟨saved.1, 1, none, some fault, actual.2.1.2, actual.2.2⟩
  | .inr _ => ⟨saved.1, 2, none, none, actual.2.1.2, actual.2.2⟩

/-- The actual bound client, the separately constructed conditional result,
and the retained read/effect trace agree at their declared data boundary. -/
theorem selected_bind_propagates_real_dependencies :
    (view completed).answer = some conditionalResult.value ∧
      (view completed).dependencies = conditionalResult.dependencies ∧
      (view completed).history = [(0, 10), (1, 1002), (2, 11)] ∧
      (view completed).paid = 3 ∧ (view cut).dependencies = {first} :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem split_resume_keeps_actual_residual_effects_and_account :
    Mettapedia.Machines.Cursor.resume (Tracked.provider step used) (Tracked.client Nat)
      (fun state operation => cost state.1 operation) 3 cut = completed :=
  (Mettapedia.Machines.Cursor.advance_add (Tracked.provider step used) (Tracked.client Nat)
    (fun state operation => cost state.1 operation) 1 3 ⟨PUnit.unit, .ok program, (0, []), ∅⟩).symm

theorem fault_retains_used_assumptions_and_prior_effect :
    (view faulted).status = 1 ∧ (view faulted).fault = some 99 ∧
      (view faulted).dependencies = {first} ∧
      (view faulted).history = [(0, 10), (1, 1002), (2, 2099)] ∧ (view faulted).paid = 3 := by decide

def jobs (owner : Bool) : Saved := if owner then faultCut else cut
def requests : List (Bool × Nat) := [(false, 3), (true, 3)]
def parallel := (Tracked.parallelKernel step used cost).batch () (fun _ => ()) jobs requests

theorem real_independent_jobs_preserve_faults_effects_and_dependencies :
    (view (parallel false)).answer = some 6 ∧
      (view (parallel true)).fault = some 99 ∧
      (view (parallel false)).dependencies ∪ (view (parallel true)).dependencies = {first, second} ∧
      (view (parallel false)).history.length + (view (parallel true)).history.length = 6 ∧
      (view (parallel false)).paid + (view (parallel true)).paid = 6 := by decide

theorem real_independent_jobs_equal_serial_full_states :
    parallel = (Tracked.parallelKernel step used cost).run () (fun _ => ()) jobs requests :=
  Tracked.parallel_is_serial_on_independent_owners step used cost jobs requests (by decide)

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def requirement : CheckedGrant.Requirement Nat Nat Access := ⟨⟨0, 9, 3⟩, .consume⟩
def current : CheckedGrant.View Nat Nat Access := ⟨⟨0, 9, 3⟩, .consume⟩
def revoked : CheckedGrant.View Nat Nat Access := ⟨⟨0, 9, 3⟩, .none⟩
def regranted : CheckedGrant.View Nat Nat Access := ⟨⟨0, 9, 4⟩, .consume⟩

local instance grantDecision (grant : CheckedGrant.View Nat Nat Access) :
    Decidable (FrameUpdate grant.available requirement.required) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate grant.available frame = true → Access.separate Access.consume frame = true))

def active (fact : Fact) : Bool := fact.scope.epoch == 3
def adoptionView : Except (Conditional premiseMeaning positiveNaturals) (Conditional premiseMeaning positiveNaturals) →
    Bool × Nat × Finset Fact
  | .ok result => (true, result.value, result.dependencies)
  | .error result => (false, result.value, result.dependencies)

/-- A policy can rely on a false external claim without turning it into a
checked theorem. Its false named premise remains explicit in the result. -/
theorem adopted_data_does_not_establish_its_claim :
    adoptionView (adopt premiseMeaning requirement current active (report positiveNaturals falseReport)) =
        (true, 0, {falseReport}) ∧
      ¬ positiveNaturals.Meaning (0 : Nat) := by
  exact ⟨by decide, fun purported => purported rfl⟩

theorem revocation_and_equal_right_regrant_preserve_original_premises :
    adoptionView (adopt premiseMeaning requirement revoked active conditionalResult) =
        (false, 6, {first, second}) ∧
      adoptionView (adopt premiseMeaning requirement regranted active conditionalResult) =
        (false, 6, {first, second}) ∧
      adoptionView (adopt premiseMeaning requirement current (fun _ => false) conditionalResult) =
        (false, 6, {first, second}) := by decide

theorem refusal_does_not_rewrite_historical_verdicts :
    ((publish premiseMeaning requirement revoked active [report positiveNaturals first] conditionalResult).1.map
      (fun result => (result.value, result.dependencies))) = [((2 : Nat), {first})] := rfl


theorem concrete_refusal_is_not_absence_or_an_erasure_licence :
    original (adopt premiseMeaning requirement revoked active conditionalResult) = conditionalResult ∧
      ¬ (discardRefused (target := positiveNaturals) premiseMeaning requirement revoked active).ErasurePreserves (reviewStable premiseMeaning)
        (fun state => (reviewRead premiseMeaning state).dependencies) (fun _ => ∅) := by
  refine ⟨adoption_returns_original premiseMeaning requirement revoked active conditionalResult, ?_⟩
  exact refusal_does_not_license_erasing_named_assumptions premiseMeaning requirement revoked active conditionalResult
    rfl (by decide)


namespace ReportedClient

abbrev Op := Fact ⊕ Nat
def targets (_operation : Op) := positiveNaturals
abbrev Reply (operation : Op) := Conditional premiseMeaning (targets operation)

def step (state : State) (operation : Op) : State × Except Nat (Reply operation) :=
  match operation with
  | .inl fact => ((state.1 + 1, state.2 ++ [(state.1, fact.occurrence)]), .ok (report positiveNaturals fact))
  | .inr code => ((state.1 + 1, state.2 ++ [(state.1, 2000 + code)]), .error code)

abbrev used : State → (operation : Op) → Except Nat (Reply operation) → Finset Fact :=
  Reported.dependencies premiseMeaning targets
abbrev Answer := Conditional premiseMeaning positiveNaturals

def firstCall : Prog Op Reply Answer := .call (.inl first) .ret
def next (firstResult : Answer) : Prog Op Reply Answer :=
  .call (.inl second) fun secondResult => .ret ((firstResult.pair secondResult).map sumPositive)
def program := firstCall.bind next

def run (fuel : Nat) := Tracked.slice step used (fun _ _ => 1) fuel program (0, []) ∅
def decoded (fuel : Nat) := PrimitiveProgram.readOutcome (Tracked.handle step used) (run fuel).2

theorem actual_conditional_replies_compose_in_the_selected_bound_client :
    (match (decoded 3).1 with | .inl (.ok result) => some (result.value, result.dependencies) | _ => none) =
        some (conditionalResult.value, conditionalResult.dependencies) ∧
      (decoded 3).2.2 = conditionalResult.dependencies ∧
      (decoded 3).2.1.2 = [(0, 10), (1, 11)] ∧ (run 3).1 = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem actual_reported_client_keeps_the_same_residual_on_resume :
    Mettapedia.Machines.Cursor.resume (Tracked.provider step used) (Tracked.client Answer)
      (fun _ _ => 1) 2 (run 1) = run 3 :=
  (Mettapedia.Machines.Cursor.advance_add (Tracked.provider step used) (Tracked.client Answer)
    (fun _ _ => 1) 1 2 ⟨PUnit.unit, .ok program, (0, []), ∅⟩).symm

end ReportedClient

end Controls

end Reliance

end Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation
