import Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServices
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mettapedia.OSLF.Syntax.BindingEqualityWire
import Mettapedia.OSLF.Syntax.FiniteRuleProofData

/-!
# Exact external packets for the declared scoped rho services

Packets retain the fixed declaration environment, source context, service
role, actual native telescope/type/terms, and every submitted equality field.
Native syntax uses the existing declaration-aware Pattern codec. Equality
uses either the existing sorted binding-signature evidence codec or the
registered explicit native structural proof wire. The selected role fixes
which evidence decoder is used. Canonical whole packet decoding refuses
alternative encodings and trailing input.

Execution remains the existing direct native operation. Its response carries
its actual computed result; checking a proposed result is a distinct packet.
The packet boundary supplies no executed asymptotic resource bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServiceWire

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open ScopedRepresentation ScopedRepresentation.DeclarationProfile
open ScopedServices

private abbrev pattern := Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker

/-- Compact scalars reuse the shared structural UTF-8/binary codec. This is
packet data; a scalar's Pattern representation is not an authored variable. -/
def compactScalar {α : Type} (codec : Codec α) :
    PartialCodec α Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.binaryScalar codec

def compactScalars : ScalarCodecs := Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.binaryScalars

private abbrev compactHead := WithScalars.towerHeadCodec compactScalars

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices (sorts operators)

/-- The original native syntax codec is lifted through the existing exact
Pattern data codec; all native scope checks stay in its original decoder. -/
def nativeTerm (arity : Nat) : Codec (Operations.NativeTerm arity) :=
  pattern.mapped (WithScalars.encodeTm compactScalars compactHead)
    (WithScalars.decodeTm? compactScalars compactHead arity)
    (WithScalars.decodeTm?_encodeTm compactScalars compactHead)

def nativeContext (arity : Nat) : Codec (Tower.Ctx arity) :=
  pattern.mapped (WithScalars.encodeCtx compactScalars compactHead)
    (WithScalars.decodeCtx? compactScalars compactHead arity)
    (WithScalars.decodeCtx?_encodeCtx compactScalars compactHead)

def termRequest (arity : Nat) : Codec (TermRequest arity) :=
  (Codec.prod (nativeContext arity) (Codec.prod (nativeTerm arity) (nativeTerm arity))).mapped
    (fun request => (request.context, (request.term, request.type)))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩) (fun _ => rfl)

private def bit : Codec Bool := Codec.nat.mapped (fun value => if value then 1 else 0)
  (fun value => match value with | 0 => some false | 1 => some true | _ => none)
  (fun value => by cases value <;> rfl)

def operation (context : Mettapedia.OSLF.Binding.Ctx sig) : Codec (OperationRequest context) :=
  (Codec.prod (termRequest context.length) (Codec.list bit)).mapped
    (fun request => (request.argument, request.address))
    (fun value => some ⟨value.1, value.2⟩) (fun _ => rfl)

def equation (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt) :
    Codec (EquationRequest context.length × EquationEvidence context sort) :=
  Codec.prod (Codec.prod (termRequest context.length) (termRequest context.length))
    (EqualityCertificates.Wire.certificate sorts operators rhoSourceE context sort)

/-! ## Literal native structural-rule proof wires -/

namespace NativeEquations
open Mettapedia.OSLF.NativeTypes.Certificates

private inductive RuleKind where
  | refl
  | symm
  | trans
  | parallelComm
  | parallelAssoc
  | parallelUnit
  | nameEta
  | parallelCong
  | outputCong
  | inputCong
  | quoteCong
  | dropCong
  deriving DecidableEq

private def putRuleKind : RuleKind → Nat
  | .refl => 0
  | .symm => 1
  | .trans => 2
  | .parallelComm => 3
  | .parallelAssoc => 4
  | .parallelUnit => 5
  | .nameEta => 6
  | .parallelCong => 7
  | .outputCong => 8
  | .inputCong => 9
  | .quoteCong => 10
  | .dropCong => 11
private def getRuleKind : Nat → Option RuleKind
  | 0 => some .refl
  | 1 => some .symm
  | 2 => some .trans
  | 3 => some .parallelComm
  | 4 => some .parallelAssoc
  | 5 => some .parallelUnit
  | 6 => some .nameEta
  | 7 => some .parallelCong
  | 8 => some .outputCong
  | 9 => some .inputCong
  | 10 => some .quoteCong
  | 11 => some .dropCong
  | _ => none

private def ruleKinds : Codec RuleKind :=
  Codec.nat.mapped putRuleKind getRuleKind (fun kind => by cases kind <;> rfl)

private def unit : Codec Unit where
  put _ := .atom 0
  get | .atom 0 => some () | _ => none
  get_put _ := rfl

private def RuleFields (context : Mettapedia.OSLF.Binding.Ctx sig) : RuleKind → Type
  | .refl => (Srt × (Operations.NativeTerm context.length × Unit))
  | .symm => (Srt × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit)))
  | .trans => (Srt × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))))
  | .parallelComm => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))
  | .parallelAssoc => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit)))
  | .parallelUnit => (Operations.NativeTerm context.length × Unit)
  | .nameEta => (Operations.NativeTerm context.length × Unit)
  | .parallelCong => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))))
  | .outputCong => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))))
  | .inputCong => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × (Operations.NativeTerm (context.length + 1) × (Operations.NativeTerm (context.length + 1) × Unit))))
  | .quoteCong => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))
  | .dropCong => (Operations.NativeTerm context.length × (Operations.NativeTerm context.length × Unit))

private def ruleFields (context : Mettapedia.OSLF.Binding.Ctx sig) :
    (kind : RuleKind) → Codec (RuleFields context kind)
  | .refl => (Codec.prod (sorts) (Codec.prod (nativeTerm context.length) unit))
  | .symm => (Codec.prod (sorts) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit)))
  | .trans => (Codec.prod (sorts) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))))
  | .parallelComm => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))
  | .parallelAssoc => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit)))
  | .parallelUnit => (Codec.prod (nativeTerm context.length) unit)
  | .nameEta => (Codec.prod (nativeTerm context.length) unit)
  | .parallelCong => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))))
  | .outputCong => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))))
  | .inputCong => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm (context.length + 1)) (Codec.prod (nativeTerm (context.length + 1)) unit))))
  | .quoteCong => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))
  | .dropCong => (Codec.prod (nativeTerm context.length) (Codec.prod (nativeTerm context.length) unit))

private def packRule : Conversion.Explicit.Rule →
    (Σ context : Mettapedia.OSLF.Binding.Ctx sig, Σ kind : RuleKind, RuleFields context kind)
  | .refl context sort term => ⟨context, .refl, (sort, (term, ()))⟩
  | .symm context sort first second => ⟨context, .symm, (sort, (first, (second, ())))⟩
  | .trans context sort first middle last => ⟨context, .trans, (sort, (first, (middle, (last, ()))))⟩
  | .parallelComm context first second => ⟨context, .parallelComm, (first, (second, ()))⟩
  | .parallelAssoc context first second third => ⟨context, .parallelAssoc, (first, (second, (third, ())))⟩
  | .parallelUnit context term => ⟨context, .parallelUnit, (term, ())⟩
  | .nameEta context term => ⟨context, .nameEta, (term, ())⟩
  | .parallelCong context first first' second second' => ⟨context, .parallelCong, (first, (first', (second, (second', ()))))⟩
  | .outputCong context name name' payload payload' => ⟨context, .outputCong, (name, (name', (payload, (payload', ()))))⟩
  | .inputCong context name name' body body' => ⟨context, .inputCong, (name, (name', (body, (body', ()))))⟩
  | .quoteCong context first second => ⟨context, .quoteCong, (first, (second, ()))⟩
  | .dropCong context first second => ⟨context, .dropCong, (first, (second, ()))⟩

private def unpackRule :
    (Σ context : Mettapedia.OSLF.Binding.Ctx sig, Σ kind : RuleKind, RuleFields context kind) →
      Conversion.Explicit.Rule
  | ⟨context, .refl, (sort, (term, ()))⟩ => .refl context sort term
  | ⟨context, .symm, (sort, (first, (second, ())))⟩ => .symm context sort first second
  | ⟨context, .trans, (sort, (first, (middle, (last, ()))))⟩ => .trans context sort first middle last
  | ⟨context, .parallelComm, (first, (second, ()))⟩ => .parallelComm context first second
  | ⟨context, .parallelAssoc, (first, (second, (third, ())))⟩ => .parallelAssoc context first second third
  | ⟨context, .parallelUnit, (term, ())⟩ => .parallelUnit context term
  | ⟨context, .nameEta, (term, ())⟩ => .nameEta context term
  | ⟨context, .parallelCong, (first, (first', (second, (second', ()))))⟩ => .parallelCong context first first' second second'
  | ⟨context, .outputCong, (name, (name', (payload, (payload', ()))))⟩ => .outputCong context name name' payload payload'
  | ⟨context, .inputCong, (name, (name', (body, (body', ()))))⟩ => .inputCong context name name' body body'
  | ⟨context, .quoteCong, (first, (second, ()))⟩ => .quoteCong context first second
  | ⟨context, .dropCong, (first, (second, ()))⟩ => .dropCong context first second

/-- Literal scope and all native endpoints use their existing scoped codec.
Input bodies retain their extra bound-variable position. -/
def rule : Codec Conversion.Explicit.Rule :=
  (Codec.sigma (Codec.list sorts) (fun context => Codec.sigma ruleKinds (ruleFields context))).mapped
    packRule (some ∘ unpackRule) (fun code => by cases code <;> rfl)

abbrev Wire := Tree.Wire Conversion.Explicit.presentation

/-- The existing arbitrary-label finite proof wire retains missing/extra
children for the original proof decoder to check. -/
def proof : Codec Wire := FiniteRuleLabelledProofWire.wireCodec rule

/-- Decode the original finite proof history and invoke the registered
native-proof service on the unchanged displayed native equation. -/
def invoke? {context : Mettapedia.OSLF.Binding.Ctx sig} (sort : Srt)
    (input : EquationRequest context.length) (wire : Wire) : Option (EquationRequest context.length) := do
  let decoded ← Tree.decodeDerivation wire
  (invokeRouted (nativeEquationRequest (sort := sort) input (Tree.erase decoded.2))).acceptedValue

theorem invoke_sound {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (wire : Wire)
    (accepted : invoke? sort input wire = some input) : EquationMeaning context sort input := by
  unfold invoke? at accepted
  cases decoded : Tree.decodeDerivation wire with
  | none => simp only [decoded, Bind.bind, Option.bind] at accepted; cases accepted
  | some history =>
      simp only [decoded, Bind.bind, Option.bind] at accepted
      exact routed_accepted_meaning (nativeEquationRequest (sort := sort) input (Tree.erase history.2))
        .nativeProof accepted

theorem invoke_bound {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (wire : Wire) (output : EquationRequest context.length)
    (accepted : invoke? sort input wire = some output) : output = input := by
  unfold invoke? at accepted
  cases decoded : Tree.decodeDerivation wire with
  | none => simp only [decoded, Bind.bind, Option.bind] at accepted; cases accepted
  | some history =>
      simp only [decoded, Bind.bind, Option.bind] at accepted
      change (if ExplicitEquations.check context sort input (Tree.erase history.2)
        then some input else none) = some output at accepted
      split at accepted
      · exact (Option.some.inj accepted).symm
      · cases accepted

theorem invoke_encoded {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length)
    (history : Conversion.Explicit.Derivation (ExplicitEquations.claim sort input))
    (before : Admitted context sort input.1) (after : Admitted context sort input.2) :
    invoke? sort input (Tree.encodeDerivation history) = some input := by
  unfold invoke?
  have decoded := Tree.decode_encodeDerivation (P := Conversion.Explicit.presentation) history
  simp only [decoded, Bind.bind, Option.bind]
  apply (routed_native_equation_exact input (Tree.erase history)).mpr
  simp only [ExplicitEquations.check, (checkAdmission_exact input.1).mpr before,
    (checkAdmission_exact input.2).mpr after, Bool.and_self, Bool.true_and]
  exact Tree.check_erase history

/-- Accepted wire evidence is the exact encoding of an original indexed
proof history, and that same history is judged by the registered native guest. -/
theorem invoke_exact {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (input : EquationRequest context.length) (wire : Wire) :
    invoke? sort input wire = some input ↔
      ∃ history : (Σ claim : Conversion.Explicit.presentation.Judgment,
          Conversion.Explicit.presentation.Derivation claim),
        Tree.encodeDerivation history.2 = wire ∧
        (ExplicitEquations.guest context sort).Judges (Tree.erase history.2) input := by
  constructor
  · intro accepted
    unfold invoke? at accepted
    cases decoded : Tree.decodeDerivation wire with
    | none => simp only [decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some history =>
        simp only [decoded, Bind.bind, Option.bind] at accepted
        have checked := (routed_native_equation_exact input (Tree.erase history.2)).mp accepted
        exact ⟨history, Tree.encode_decodeDerivation wire history decoded,
          ((ExplicitEquations.kernel context sort).correct input (Tree.erase history.2)).mp checked⟩
  · rintro ⟨history, encoded, judged⟩
    unfold invoke?
    rw [← encoded]
    have decoded := Tree.decode_encodeDerivation history.2
    simp only [decoded, Bind.bind, Option.bind]
    exact (routed_native_equation_exact input (Tree.erase history.2)).mpr
      (((ExplicitEquations.kernel context sort).correct input (Tree.erase history.2)).mpr judged)

end NativeEquations

inductive Kind where
  | admission | equation | execution | proposedResult | nativeEquation
  deriving DecidableEq, Repr

private def putKind : Kind → Nat
  | .admission => 0 | .equation => 1 | .execution => 2 | .proposedResult => 3
  | .nativeEquation => 4
private def getKind : Nat → Option Kind
  | 0 => some .admission | 1 => some .equation | 2 => some .execution
  | 3 => some .proposedResult | 4 => some .nativeEquation | _ => none
private def kinds : Codec Kind := Codec.nat.mapped putKind getKind (fun kind => by cases kind <;> rfl)

/-- These are only the existing service inputs, arranged for transport. -/
def Fields (context : Mettapedia.OSLF.Binding.Ctx sig) : Kind → Type
  | .admission => Σ _sort : Srt, TermRequest context.length
  | .equation => Σ sort : Srt, EquationRequest context.length × EquationEvidence context sort
  | .nativeEquation => Σ _sort : Srt, EquationRequest context.length × NativeEquations.Wire
  | .execution => OperationRequest context
  | .proposedResult => OperationRequest context × Operations.NativeTerm context.length

abbrev Packet := Σ context : Mettapedia.OSLF.Binding.Ctx sig, Σ kind : Kind, Fields context kind

private def fields (context : Mettapedia.OSLF.Binding.Ctx sig) : (kind : Kind) → Codec (Fields context kind)
  | .admission => Codec.sigma sorts (fun _ => termRequest context.length)
  | .equation => Codec.sigma sorts (equation context)
  | .nativeEquation => Codec.sigma sorts (fun _ =>
      Codec.prod (Codec.prod (termRequest context.length) (termRequest context.length))
        NativeEquations.proof)
  | .execution => operation context
  | .proposedResult => Codec.prod (operation context) (nativeTerm context.length)

private def payload : Codec Packet :=
  Codec.sigma (Codec.list sorts) (fun context => Codec.sigma kinds (fields context))

/-- The complete literal environment is checked, including the native type
of every sort and constructor. A supplied header cannot install new rules. -/
@[irreducible] def declarationHeader : Data :=
  pattern.put (.apply "rho-native-services-compact-v1"
    (declarations.map fun entry => .apply "declaration"
      [compactScalars.declaration.encode entry.1,
        WithScalars.encodeTm compactScalars compactHead entry.2.type]))

private def withHeader (header : Data) : Codec Packet where
  put value := .pair header (payload.put value)
  get
    | .pair environment body => if environment = header then payload.get body else none
    | _ => none
  get_put value := by
    change (if header = header then payload.get (payload.put value) else none) = some value
    rw [if_pos rfl, payload.get_put]

def packet : Codec Packet := withHeader declarationHeader

/-- Fully canonical binary requests bind every header, field and physical
symbol. The parser is bounded by the actual finite input. -/
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


/-! ## Existing service execution and its bound response -/

def respond? : Packet → Option Data
  | ⟨context, .admission, ⟨sort, request⟩⟩ =>
      if checkAdmission context sort request then some (Data.atom 0) else none
  | ⟨context, .equation, ⟨sort, request, proof⟩⟩ =>
      if checkEquation context sort request proof then some (Data.atom 0) else none
  | ⟨_, .nativeEquation, ⟨sort, request, proof⟩⟩ => do
      let _ ← NativeEquations.invoke? sort request proof
      return Data.atom 0
  | ⟨context, .execution, request⟩ => do
      let reply ← invokeOperation? request
      return (nativeTerm context.length).put (← reply.2)
  | ⟨_, .proposedResult, ⟨request, result⟩⟩ =>
      if checkProposedResult request result then some (Data.atom 0) else none

/-- Meaning is stated by the independent source/native observations. It
contains neither successful decoding nor a supplied correctness predicate. -/
def ReplyMeaning : Packet → Data → Prop
  | ⟨context, .admission, ⟨sort, request⟩⟩, output =>
      output = .atom 0 ∧ Admitted context sort request
  | ⟨context, .equation, ⟨sort, request, _⟩⟩, output =>
      output = .atom 0 ∧ EquationMeaning context sort request
  | ⟨context, .nativeEquation, ⟨sort, request, _⟩⟩, output =>
      output = .atom 0 ∧ EquationMeaning context sort request
  | ⟨context, .execution, request⟩, output =>
      ∃ result, (nativeTerm context.length).put result = output ∧
        OperationMeaning (request, some result)
  | ⟨context, .proposedResult, ⟨request, result⟩⟩, output =>
      output = .atom 0 ∧ Admitted context .pr request.argument ∧
        Selection.Step request.address request.argument.term result

theorem respond_sound (value : Packet) (output : Data)
    (accepted : respond? value = some output) : ReplyMeaning value output := by
  obtain ⟨context, kind, fields⟩ := value
  cases kind with
  | admission =>
      obtain ⟨sort, request⟩ := fields
      change (if checkAdmission context sort request then some (Data.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i admitted
        exact ⟨(Option.some.inj accepted).symm, (checkAdmission_exact request).mp admitted⟩
      · cases accepted
  | equation =>
      obtain ⟨sort, request, proof⟩ := fields
      change (if checkEquation context sort request proof then some (Data.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i admitted
        exact ⟨(Option.some.inj accepted).symm, equationChecker_sound request proof admitted⟩
      · cases accepted
  | nativeEquation =>
      obtain ⟨sort, request, proof⟩ := fields
      change ((NativeEquations.invoke? sort request proof).bind
        (fun _ => some (Data.atom 0))) = some output at accepted
      cases computed : NativeEquations.invoke? sort request proof with
      | none => simp only [computed, Option.bind_none] at accepted; cases accepted
      | some returned =>
          have bound := NativeEquations.invoke_bound request proof returned computed
          subst returned
          simp only [computed, Option.bind_some, Option.some.injEq] at accepted
          exact ⟨accepted.symm, NativeEquations.invoke_sound request proof computed⟩
  | execution =>
      change (do
        let reply ← invokeOperation? fields
        return (nativeTerm context.length).put (← reply.2)) = some output at accepted
      cases produced : invokeOperation? fields with
      | none => simp [produced] at accepted
      | some reply =>
          have meaning := invokeOperation_sound fields reply produced
          obtain ⟨returnedRequest, returnedResult⟩ := reply
          dsimp only [Prod.fst] at meaning
          have bound := meaning.1
          subst returnedRequest
          cases result : returnedResult with
          | none => simp [produced, result] at accepted
          | some target =>
              simp only [produced, result, Bind.bind, Option.bind, pure] at accepted
              exact ⟨target, Option.some.inj accepted, by simpa only [result] using meaning.2⟩
  | proposedResult =>
      obtain ⟨request, result⟩ := fields
      change (if checkProposedResult request result then some (Data.atom 0) else none) = some output at accepted
      split at accepted
      · rename_i checked
        have checks : checkOperation request = true ∧
            Selection.executeAt? request.address request.argument.term = some result := by
          simpa only [checkProposedResult, Bool.and_eq_true, decide_eq_true_eq] using checked
        exact ⟨(Option.some.inj accepted).symm, ((checkOperation_exact request).mp checks.1).1,
          (Selection.executeAt_exact _ _ _).mp checks.2⟩
      · cases accepted

theorem respond_admission {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : TermRequest context.length) (admitted : Admitted context sort request) :
    respond? ⟨context, .admission, ⟨sort, request⟩⟩ = some (Data.atom 0) := by
  change (if checkAdmission context sort request then some (Data.atom 0) else none) = _
  rw [(checkAdmission_exact request).mpr admitted]
  rfl

theorem respond_equation {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (proof : EquationEvidence context sort)
    (accepted : checkEquation context sort request proof = true) :
    respond? ⟨context, .equation, ⟨sort, request, proof⟩⟩ = some (Data.atom 0) := by
  change (if checkEquation context sort request proof then some (Data.atom 0) else none) = _
  rw [accepted]
  rfl

theorem respond_nativeEquation {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (proof : NativeEquations.Wire)
    (accepted : NativeEquations.invoke? sort request proof = some request) :
    respond? ⟨context, .nativeEquation, ⟨sort, request, proof⟩⟩ = some (Data.atom 0) := by
  change ((NativeEquations.invoke? sort request proof).bind
    (fun _ => some (Data.atom 0))) = _
  rw [accepted]
  rfl

theorem respond_execution {context : Mettapedia.OSLF.Binding.Ctx sig}
    (request : OperationRequest context) (result : Operations.NativeTerm context.length)
    (admitted : Admitted context .pr request.argument)
    (step : Selection.Step request.address request.argument.term result) :
    respond? ⟨context, .execution, request⟩ = some ((nativeTerm context.length).put result) := by
  change (do
    let reply ← invokeOperation? request
    return (nativeTerm context.length).put (← reply.2)) = _
  rw [(invokeOperation_some_iff request result).mpr ⟨admitted, step⟩]
  rfl

/-- The physical reply contains the entire original request, including its
proof packet when present, before the actual response payload. -/
def run (word : List Alphabet) : Option (List Alphabet) := do
  let value ← decodeRequest word
  let output ← respond? value
  return encodeData (.pair (packet.put value) output)

theorem run_exact (word response : List Alphabet) : run word = some response ↔
    ∃ value output, encodeRequest value = word ∧ respond? value = some output ∧
      encodeData (.pair (packet.put value) output) = response := by
  constructor
  · intro accepted
    unfold run at accepted
    cases decoded : decodeRequest word with
    | none => simp only [decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some value =>
        cases responded : respond? value with
        | none =>
            simp only [decoded, responded, Bind.bind, Option.bind] at accepted
            cases accepted
        | some output =>
            simp only [decoded, responded, Bind.bind, Option.bind, pure,
              Option.some.injEq] at accepted
            exact ⟨value, output, (decodeRequest_exact word value).mp decoded, responded, accepted⟩
  · rintro ⟨value, output, encoded, responded, actual⟩
    unfold run
    rw [(decodeRequest_exact word value).mpr encoded]
    simp only [Bind.bind, Option.bind]
    rw [responded]
    exact congrArg some actual

theorem run_sound (word response : List Alphabet) (accepted : run word = some response) :
    ∃ value output, encodeRequest value = word ∧ ReplyMeaning value output ∧
      encodeData (.pair (packet.put value) output) = response := by
  obtain ⟨value, output, encoded, responded, actual⟩ := (run_exact word response).mp accepted
  exact ⟨value, output, encoded, respond_sound value output responded, actual⟩

theorem run_encoded (value : Packet) (output : Data) (responded : respond? value = some output) :
    run (encodeRequest value) = some (encodeData (.pair (packet.put value) output)) :=
  (run_exact _ _).mpr ⟨value, output, rfl, responded, rfl⟩

theorem run_trailing_refused (value : Packet) (tail : List Alphabet)
    (nonempty : tail.isEmpty = false) : run (encodeRequest value ++ tail) = none := by
  simp only [run, request_trailing_refused value tail nonempty, Bind.bind, Option.bind]

/-- Every meaningful native equation request has an actual accepted binary
packet. The submitted proof remains part of the retained physical request. -/
theorem equation_binary_complete {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (meaning : EquationMeaning context sort request) :
    ∃ proof : EquationEvidence context sort,
      run (encodeRequest ⟨context, .equation, ⟨sort, request, proof⟩⟩) =
        some (encodeData (.pair (packet.put ⟨context, .equation, ⟨sort, request, proof⟩⟩) (.atom 0))) := by
  obtain ⟨proof, accepted⟩ := equationChecker_complete request meaning
  exact ⟨proof, run_encoded _ _ (respond_equation request proof accepted)⟩

/-- Every independently meaningful equation also has an external explicit
native-proof request in the separately registered proof language. -/
theorem native_equation_binary_complete {context : Mettapedia.OSLF.Binding.Ctx sig} {sort : Srt}
    (request : EquationRequest context.length) (meaning : EquationMeaning context sort request) :
    ∃ proof : NativeEquations.Wire,
      run (encodeRequest ⟨context, .nativeEquation, ⟨sort, request, proof⟩⟩) =
        some (encodeData (.pair
          (packet.put ⟨context, .nativeEquation, ⟨sort, request, proof⟩⟩) (.atom 0))) := by
  obtain ⟨history⟩ := Conversion.Explicit.derivation_complete meaning.2.2
  exact ⟨_, run_encoded _ _ (respond_nativeEquation request _
    (NativeEquations.invoke_encoded request history meaning.1 meaning.2.1))⟩

/-- Every independently stated source-image native parallel step has an
addressed external request returning the actual native result bytes. -/
theorem native_step_binary_complete {context : Mettapedia.OSLF.Binding.Ctx sig}
    (source : Term sig context Srt.pr) (target : Operations.NativeTerm context.length)
    (step : Operations.ParallelStep (Inversion.E source) target) :
    ∃ address : Selection.Address,
      run (encodeRequest ⟨context, .execution, ⟨sourceRequest source, address⟩⟩) =
        some (encodeData (.pair
          (packet.put ⟨context, .execution, ⟨sourceRequest source, address⟩⟩)
          ((nativeTerm context.length).put target))) := by
  obtain ⟨address, executed⟩ := (Selection.parallel_iff_execution _ _).mp step
  exact ⟨address, run_encoded _ _ (respond_execution _ target
    (sourceRequest_admitted source) ((Selection.executeAt_exact _ _ _).mp executed))⟩

/-- The external selected execution retains the guarded authored-source
comparison. Immediate results are compared by residual equivalence, which
must not be strengthened to structural congruence. -/
theorem guarded_authored_binary (arguments : AuthoredAdapter.Arguments)
    (safe : AuthoredAdapter.quoteSafe arguments = true) :
    run (encodeRequest ⟨[], .execution, AuthoredAdapter.request arguments⟩) =
      some (encodeData (.pair
        (packet.put ⟨[], .execution, AuthoredAdapter.request arguments⟩)
        ((nativeTerm 0).put (Inversion.E (AuthoredAdapter.result arguments))))) ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
      (RhoAuthoredCommRuleCover.authoredInputFirst arguments.channel arguments.payload arguments.body)
      (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body) ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.ProcResidualEquiv
      (RhoAuthoredCommRuleCover.authoredResult arguments.payload arguments.body)
      (RhoSchema.IntrinsicEncoding.encodeTerm (AuthoredAdapter.result arguments)) := by
  have executed := AuthoredAdapter.communication_executes
    arguments.channel arguments.payload arguments.body
  have selected := (invokeOperation_some_iff (AuthoredAdapter.request arguments)
    (Inversion.E (AuthoredAdapter.result arguments))).mp executed
  have comparison := AuthoredAdapter.guarded_comparison arguments safe
  exact ⟨run_encoded _ _ (respond_execution _ _ selected.1 selected.2),
    comparison.2.2.1, comparison.2.2.2.2⟩

end Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedServiceWire
