import Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServiceWire
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Emission

/-!
# Shared explicit evidence for the scoped native rho profile

The certificate is the existing chronological rule/reference format. The
checker retains literal judgments only and agrees on every success and
refusal with the original derivation reconstruction. Its semantic observer
is the existing native structural relation, with literal scoped endpoint
admission. Sharing here is proof sharing, not operational event identity.

The graph certificate language differs from the original tree language;
proof existence is preserved without a claim of equality of proof fibres.
Comparison counts are distinct from a whole checker machine clock. The
complete-image equality machine below charges its own binary-word steps,
with serialization and cache access left as separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedSharedEvidence

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.GSLT.LanguageDef
open SemanticEvidence
open ScopedRepresentation ScopedRepresentation.Operations
open ScopedServices

abbrev Claim := Conversion.Explicit.Claim
abbrev Proof := Shared.Certificate Conversion.Explicit.presentation
abbrev Row := Shared.Row Conversion.Explicit.presentation

private instance : DecidableEq Conversion.Explicit.presentation.Judgment :=
  inferInstanceAs (DecidableEq Claim)

/-- The direct checker validates every row, including rows not used by the
selected root. Refusal is identical to the original reconstruction path. -/
def checkClaim (claim : Claim) (proof : Proof) : Bool :=
  Shared.checkJudgments proof claim

theorem checkClaim_eq_original (claim : Claim) (proof : Proof) :
    checkClaim claim proof = Shared.check proof claim :=
  Shared.checkJudgments_eq_check proof claim

theorem checkClaim_sound (claim : Claim) (proof : Proof)
    (accepted : checkClaim claim proof = true) : Conversion.Explicit.Meaning claim := by
  obtain ⟨derivation, _, _⟩ := Shared.checkJudgments_original proof claim accepted
  exact Conversion.Explicit.derivation_sound derivation

/-- Every original independent structural derivation has accepted shared
explicit evidence. This is an existence theorem, not a tree-fibre bijection. -/
theorem checkClaim_complete (claim : Claim) :
    Conversion.Explicit.Meaning claim ↔ ∃ proof : Proof, checkClaim claim proof = true := by
  constructor
  · intro equation
    obtain ⟨derivation⟩ := Conversion.Explicit.derivation_complete equation
    refine ⟨Shared.emit derivation, ?_⟩
    rw [checkClaim_eq_original]
    exact Shared.emit_checked derivation
  · rintro ⟨proof, accepted⟩
    exact checkClaim_sound claim proof accepted

/-- Graph proof relevance is its original reconstructible reference history,
qualified by independent admission of both literal native endpoints. -/
def guest (context : Ctx sig) (sort : Srt) :
    NativeProofSystem (EquationRequest context.length) where
  ProofObject := Proof
  Judges proof input := Admitted context sort input.1 ∧ Admitted context sort input.2 ∧
    (Shared.reconstruct? proof (ExplicitEquations.claim sort input)).isSome = true

def check (context : Ctx sig) (sort : Srt) (input : EquationRequest context.length)
    (proof : Proof) : Bool :=
  checkAdmission context sort input.1 && checkAdmission context sort input.2 &&
    checkClaim (ExplicitEquations.claim sort input) proof

def kernel (context : Ctx sig) (sort : Srt) : NativeProofKernel (guest context sort) where
  decide := check context sort
  correct input proof := by
    change Proof at proof
    change check context sort input proof = true ↔
      Admitted context sort input.1 ∧ Admitted context sort input.2 ∧
        (Shared.reconstruct? proof (ExplicitEquations.claim sort input)).isSome = true
    simp only [check, checkClaim_eq_original, Bool.and_eq_true, checkAdmission_exact, Shared.check]
    exact and_assoc

theorem meaning_exact (context : Ctx sig) (sort : Srt) (input : EquationRequest context.length) :
    EquationMeaning context sort input ↔ Nonempty ((guest context sort).ProofFibre input) := by
  constructor
  · rintro ⟨firstAdmitted, secondAdmitted, equation⟩
    obtain ⟨proof, accepted⟩ := (checkClaim_complete (ExplicitEquations.claim sort input)).mp equation
    have original := accepted
    rw [checkClaim_eq_original] at original
    exact ⟨⟨proof, firstAdmitted, secondAdmitted, original⟩⟩
  · rintro ⟨⟨proof, firstAdmitted, secondAdmitted, accepted⟩⟩
    change Proof at proof
    refine ⟨firstAdmitted, secondAdmitted, checkClaim_sound (ExplicitEquations.claim sort input) proof ?_⟩
    rw [checkClaim_eq_original]
    exact accepted

def service (context : Ctx sig) (sort : Srt) :
    SemanticService.Service (equationTarget context sort) :=
  .nativeProof (guest context sort) (kernel context sort) (meaning_exact context sort)

def request {context : Ctx sig} {sort : Srt} (input : EquationRequest context.length)
    (proof : Proof) : SemanticServiceInvocation.Request (service context sort) :=
  .nativeProof input proof

theorem invocation_exact {context : Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (proof : Proof) :
    (SemanticServiceInvocation.invoke (request (sort := sort) input proof)).acceptedValue = some input ↔
      check context sort input proof = true := by
  change (if check context sort input proof then some input else none) = some input ↔ _
  cases check context sort input proof <;> simp

theorem source_equation_iff_service {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔
      ∃ proof : Proof, (SemanticServiceInvocation.invoke
        (request (sort := sort) (sourceRequest first, sourceRequest second) proof)).acceptedValue =
          some (sourceRequest first, sourceRequest second) := by
  rw [Conversion.source_equation_iff_structural]
  constructor
  · intro equation
    obtain ⟨proof, accepted⟩ := (checkClaim_complete
      (ExplicitEquations.claim sort (sourceRequest first, sourceRequest second))).mp equation
    refine ⟨proof, (invocation_exact _ _).mpr ?_⟩
    have before := (checkAdmission_exact (sourceRequest first)).mpr (sourceRequest_admitted first)
    have after := (checkAdmission_exact (sourceRequest second)).mpr (sourceRequest_admitted second)
    simp only [check, before, after, Bool.and_self, Bool.true_and]
    exact accepted
  · rintro ⟨proof, accepted⟩
    have checked := (invocation_exact _ _).mp accepted
    exact checkClaim_sound _ proof (Bool.and_eq_true_iff.mp checked).2

/-- Direct native execution remains the original directed parallel-context
service, bracketed by independently checked shared structural evidence. -/
theorem source_step_iff_service_invocations {context : Ctx sig}
    (first second : Term sig context Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.SourceStep first second ↔
      ∃ (before after : Term sig context Srt.pr)
          (prior later : Proof) (address : Selection.Address),
        (SemanticServiceInvocation.invoke
          (request (sort := .pr) (sourceRequest first, sourceRequest before) prior)).acceptedValue =
            some (sourceRequest first, sourceRequest before) ∧
        SemanticServiceInvocation.InputAdmission
          (operationRequest ⟨sourceRequest before, address⟩) ∧
        (SemanticServiceInvocation.invoke
          (operationRequest ⟨sourceRequest before, address⟩)).acceptedValue =
            some (⟨sourceRequest before, address⟩, some (Inversion.E after)) ∧
        (SemanticServiceInvocation.invoke
          (request (sort := .pr) (sourceRequest after, sourceRequest second) later)).acceptedValue =
            some (sourceRequest after, sourceRequest second) := by
  rw [Operations.source_step_iff_native_modulo]
  constructor
  · rintro ⟨before, after, priorEquation, execution, laterEquation⟩
    obtain ⟨prior, priorAccepted⟩ := (source_equation_iff_service first before).mp priorEquation
    obtain ⟨later, laterAccepted⟩ := (source_equation_iff_service after second).mp laterEquation
    obtain ⟨address, executed⟩ := (Selection.parallel_iff_execution _ _).mp execution
    refine ⟨before, after, prior, later, address, priorAccepted, ?_, ?_, laterAccepted⟩
    · exact (operation_input_admission_exact _).mpr
        ⟨sourceRequest_admitted before, Inversion.E after,
          (Selection.executeAt_exact _ _ _).mp executed⟩
    · exact (operation_invocation_value _ _).mpr executed
  · rintro ⟨before, after, prior, later, address, priorAccepted, _, executed, laterAccepted⟩
    refine ⟨before, after, (source_equation_iff_service first before).mpr ⟨prior, priorAccepted⟩,
      ?_, (source_equation_iff_service after second).mpr ⟨later, laterAccepted⟩⟩
    exact (Selection.parallel_iff_execution _ _).mpr
      ⟨address, (operation_invocation_value _ _).mp executed⟩

/-- The existing twelve structural rules have at most two explicit premises.
There is no hidden normalization/substitution cost in this count. -/
theorem rule_premises_le (rule : Conversion.Explicit.Rule) :
    (Conversion.Explicit.presentation.premises rule).length ≤ 2 := by
  cases rule <;> simp [Conversion.Explicit.presentation, Conversion.Explicit.premises]

theorem premiseSlots_le (rows : List Row) : Shared.premiseSlots rows ≤ 2 * rows.length := by
  induction rows with
  | nil => simp [Shared.premiseSlots]
  | cons row rows ih =>
      have arity := rule_premises_le row.rule
      simp only [Shared.premiseSlots, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem comparison_work_le (claim : Claim) (proof : Proof) :
    (Shared.checkJudgmentsWithWork proof claim).2.1 ≤ proof.rows.length ∧
    (Shared.checkJudgmentsWithWork proof claim).2.2 ≤ 2 * proof.rows.length + 1 := by
  have actual := Shared.checkJudgments_work_le proof claim
  have inventory := premiseSlots_le proof.rows
  exact ⟨actual.1, by omega⟩

theorem accepted_comparison_work (claim : Claim) (proof : Proof)
    (accepted : checkClaim claim proof = true) :
    (Shared.checkJudgmentsWithWork proof claim).2.1 = proof.rows.length ∧
    (Shared.checkJudgmentsWithWork proof claim).2.2 = Shared.premiseSlots proof.rows + 1 :=
  Shared.checkJudgments_work_eq proof claim accepted

namespace Storage
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

/-- Canonical claim images retain the complete source scope, source sort and
both actual native syntax trees. All recursive syntax codecs are reused. -/
def claim : Codec Claim :=
  (Codec.sigma (Codec.list Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.sorts) fun context =>
    Codec.sigma Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.sorts fun _ =>
      Codec.prod (ScopedServiceWire.nativeTerm context.length)
        (ScopedServiceWire.nativeTerm context.length)).mapped
    (fun value => ⟨value.context, value.sort, value.first, value.second⟩)
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (fun value => by cases value; rfl)

theorem claim_roundtrip (value : Claim) : claim.get (claim.put value) = some value :=
  claim.get_put value

/-- Complete canonical claim equality runs on the original word machine;
the cost of constructing these input images is not included. -/
def comparison_outputs (first second : Claim) :
    Turing.TM2OutputsInTime
      (Mettapedia.Computability.WordEqualityMachine.machine Alphabet)
      (Equality.packet claim first second) (some [decide (first = second)])
      (3 * (encodeWith claim first).length + (encodeWith claim second).length + 4) :=
  Equality.outputs claim first second


/-- At an actual available table reference, the original word machine
computes precisely the Boolean used by the direct premise checker. A
missing reference is refused before any equality packet can be constructed. -/
def reference_outputs (table : List Claim) (rule : Row)
    (position : Fin (Conversion.Explicit.premises rule.rule).length)
    (actual : Claim) (selected : table[rule.references position]? = some actual) :
    Turing.TM2OutputsInTime (Mettapedia.Computability.WordEqualityMachine.machine Alphabet)
      (Equality.packet claim actual
        ((Conversion.Explicit.premises rule.rule).get position))
      (some [decide (table[rule.references position]? =
        some ((Conversion.Explicit.premises rule.rule).get position))])
      (3 * (encodeWith claim actual).length +
        (encodeWith claim ((Conversion.Explicit.premises rule.rule).get position)).length + 4) := by
  simpa only [selected, Option.some.injEq] using
    comparison_outputs actual ((Conversion.Explicit.premises rule.rule).get position)

/-- The arity is fixed by the decoded original rule. No extra or missing
reference can be ignored by the row decoder. -/
private def references : (arity : Nat) → Codec (Fin arity → Nat)
  | 0 =>
      { put := fun _ => .atom 0
        get := fun data => if data = .atom 0 then some Fin.elim0 else none
        get_put := fun value => by
          simp only [ite_true]
          apply congrArg some
          funext index
          exact Fin.elim0 index }
  | arity + 1 =>
      (Codec.prod Codec.nat (references arity)).mapped
        (fun value => (value 0, fun index => value index.succ))
        (fun value => some (Fin.cases value.1 value.2))
        (fun value => by
          apply congrArg some
          funext index
          cases index using Fin.cases <;> rfl)

/-- All original rule fields and all premise references survive storage. -/
def row : Codec Row :=
  (Codec.sigma ScopedServiceWire.NativeEquations.rule fun rule =>
    references (Conversion.Explicit.presentation.premises rule).length).mapped
    (fun value => ⟨value.rule, value.references⟩)
    (fun value => some ⟨value.1, value.2⟩) (fun value => by cases value; rfl)

def proof : Codec Proof :=
  (Codec.prod (Codec.list row) Codec.nat).mapped
    (fun value => (value.rows, value.root))
    (fun value => some ⟨value.1, value.2⟩) (fun value => by cases value; rfl)

theorem proof_roundtrip (value : Proof) : proof.get (proof.put value) = some value :=
  proof.get_put value

/-- This is an additive graph-proof role with its own versioned packet. The
existing compact- and tree-proof external formats are unchanged. -/
abbrev Packet := Σ context : Ctx sig, Σ _sort : Srt,
  EquationRequest context.length × Proof

private def payload : Codec Packet :=
  Codec.sigma (Codec.list Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.sorts) fun context =>
    Codec.sigma Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices.sorts fun _ =>
      Codec.prod
        (Codec.prod (ScopedServiceWire.termRequest context.length)
          (ScopedServiceWire.termRequest context.length)) proof

/-- The version selects the graph role; the original fixed declaration
header retains every installed rho declaration and its actual native type. -/
def header : Data := .pair (.atom 0) ScopedServiceWire.declarationHeader

def packet : Codec Packet where
  put value := .pair header (payload.put value)
  get
    | .pair actual body => if actual = header then payload.get body else none
    | _ => none
  get_put value := by
    change (if header = header then payload.get (payload.put value) else none) = some value
    rw [if_pos rfl, payload.get_put]

def encodeRequest (value : Packet) : List Alphabet := encodeWith packet value

def decodeRequest (word : List Alphabet) : Option Packet := canonicalDecodeWith packet word

theorem decodeRequest_encodeRequest (value : Packet) :
    decodeRequest (encodeRequest value) = some value :=
  canonicalDecodeWith_encodeWith packet value

theorem decodeRequest_exact (word : List Alphabet) (value : Packet) :
    decodeRequest word = some value ↔ encodeRequest value = word :=
  canonicalDecodeWith_exact packet word value

theorem request_trailing_refused (value : Packet) (tail : List Alphabet)
    (nonempty : tail.isEmpty = false) : decodeRequest (encodeRequest value ++ tail) = none :=
  canonicalDecodeWith_trailing_refused packet value tail nonempty

def accepted (value : Packet) : Bool :=
  check value.1 value.2.1 value.2.2.1 value.2.2.2

/-- The reply includes the complete original graph request and a success tag.
It does not expand the graph into a proof tree. -/
def reply (value : Packet) : List Alphabet :=
  encodeWith (Codec.prod packet Codec.nat) (value, 0)

def run (word : List Alphabet) : Option (List Alphabet) := do
  let value ← decodeRequest word
  if accepted value then some (reply value) else none

theorem run_encoded (value : Packet) :
    run (encodeRequest value) = if accepted value then some (reply value) else none := by
  simp only [run, decodeRequest_encodeRequest, Bind.bind, Option.bind]

theorem run_exact (word output : List Alphabet) :
    run word = some output ↔ ∃ value : Packet,
      encodeRequest value = word ∧ accepted value = true ∧ reply value = output := by
  constructor
  · intro computed
    unfold run at computed
    cases decoded : decodeRequest word with
    | none => simp only [decoded, Bind.bind, Option.bind] at computed; cases computed
    | some value =>
        simp only [decoded, Bind.bind, Option.bind] at computed
        split at computed
        · rename_i admitted
          exact ⟨value, (decodeRequest_exact word value).mp decoded, admitted,
            Option.some.inj computed⟩
        · cases computed
  · rintro ⟨value, literal, admitted, result⟩
    subst word
    rw [run_encoded, admitted]
    exact congrArg some result

/-- Native structural truth follows from the actual fixed-scope admission
and reference checks, independently of the bytes and the success tag. -/
theorem run_sound (word output : List Alphabet) (computed : run word = some output) :
    ∃ value : Packet, encodeRequest value = word ∧ reply value = output ∧
      EquationMeaning value.1 value.2.1 value.2.2.1 := by
  obtain ⟨value, literal, checked, result⟩ := (run_exact word output).mp computed
  refine ⟨value, literal, result, ?_⟩
  have judged := ((kernel value.1 value.2.1).correct value.2.2.1 value.2.2.2).mp checked
  exact (meaning_exact value.1 value.2.1 value.2.2.1).mpr ⟨⟨value.2.2.2, judged⟩⟩

theorem reply_length (value : Packet) : (reply value).length = (encodeRequest value).length + 3 := by
  change (encodeData (.pair (packet.put value) (.atom 0))).length = _
  rw [encodeData_pair]
  simp only [List.length_cons, List.length_append]
  change (encodeRequest value).length + 2 + 1 = (encodeRequest value).length + 3
  omega

theorem source_equation_iff_run {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) : EqClosure rhoSourceE first second ↔
      ∃ proof : Proof, run (encodeRequest
        ⟨context, sort, (sourceRequest first, sourceRequest second), proof⟩) = some (reply
        ⟨context, sort, (sourceRequest first, sourceRequest second), proof⟩) := by
  rw [source_equation_iff_service first second]
  constructor
  · rintro ⟨proof, invoked⟩
    refine ⟨proof, ?_⟩
    rw [run_encoded]
    have checked := (invocation_exact _ _).mp invoked
    change (if check context sort (sourceRequest first, sourceRequest second) proof then _ else _) = _
    rw [checked]
    rfl
  · rintro ⟨proof, computed⟩
    refine ⟨proof, (invocation_exact _ _).mpr ?_⟩
    rw [run_encoded] at computed
    split at computed
    · assumption
    · cases computed

/-- The graph role cannot be confused with the original compact/tree role. -/
theorem header_ne_original : header ≠ ScopedServiceWire.declarationHeader := by
  intro same
  have sizes := congrArg sizeOf same
  simp only [header, Data.pair.sizeOf_spec, Data.atom.sizeOf_spec] at sizes
  omega

theorem encoded_ne_original (value : Packet) (original : ScopedServiceWire.Packet) :
    encodeRequest value ≠ ScopedServiceWire.encodeRequest original := by
  intro same
  have encoded := encodeData_injective same
  change Data.pair header _ = Data.pair ScopedServiceWire.declarationHeader _ at encoded
  exact header_ne_original (Data.pair.inj encoded).1

theorem original_request_refused (original : ScopedServiceWire.Packet) :
    decodeRequest (ScopedServiceWire.encodeRequest original) = none := by
  cases decoded : decodeRequest (ScopedServiceWire.encodeRequest original) with
  | none => rfl
  | some value =>
      exact (encoded_ne_original value original
        ((decodeRequest_exact _ value).mp decoded)).elim

theorem graph_request_refused_by_original (value : Packet) :
    ScopedServiceWire.decodeRequest (encodeRequest value) = none := by
  cases decoded : ScopedServiceWire.decodeRequest (encodeRequest value) with
  | none => rfl
  | some original =>
      exact (encoded_ne_original value original
        ((ScopedServiceWire.decodeRequest_exact _ original).mp decoded).symm).elim

/-- Try the existing literal roles, then the version-disjoint graph role.
Each role retains its original decoder and semantic checker. -/
def runRouted (word : List Alphabet) : Option (List Alphabet) :=
  (ScopedServiceWire.run word).orElse fun _ => run word

theorem runRouted_original (value : ScopedServiceWire.Packet) :
    runRouted (ScopedServiceWire.encodeRequest value) =
      ScopedServiceWire.run (ScopedServiceWire.encodeRequest value) := by
  have refused : run (ScopedServiceWire.encodeRequest value) = none := by
    simp only [run, original_request_refused, Bind.bind, Option.bind_none]
  simp only [runRouted, refused]
  cases ScopedServiceWire.run (ScopedServiceWire.encodeRequest value) <;> rfl

theorem runRouted_graph (value : Packet) :
    runRouted (encodeRequest value) = run (encodeRequest value) := by
  have refused : ScopedServiceWire.run (encodeRequest value) = none := by
    simp only [ScopedServiceWire.run, graph_request_refused_by_original, Bind.bind, Option.bind_none]
  simp only [runRouted, refused, Option.orElse_none]

/-- Every successful dispatch has an independently checked request in one
of the two literal certificate languages. -/
theorem runRouted_sound (word output : List Alphabet)
    (computed : runRouted word = some output) :
    (∃ value result, ScopedServiceWire.encodeRequest value = word ∧
      ScopedServiceWire.ReplyMeaning value result ∧
      encodeData (.pair (ScopedServiceWire.packet.put value) result) = output) ∨
    (∃ value : Packet, encodeRequest value = word ∧ reply value = output ∧
      EquationMeaning value.1 value.2.1 value.2.2.1) := by
  unfold runRouted at computed
  cases original : ScopedServiceWire.run word with
  | none =>
      simp only [original, Option.orElse_none] at computed
      exact Or.inr (run_sound word output computed)
  | some result =>
      have same : result = output := by simpa only [original, Option.orElse_some, Option.some.injEq] using computed
      subst result
      exact Or.inl (ScopedServiceWire.run_sound word output original)

end Storage
end Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedSharedEvidence
