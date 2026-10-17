import Mettapedia.Languages.OpenTheory.SyntaxEncoding
import Mettapedia.Languages.HOLLight.StorageSize
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

/-!
# Executable finite-alphabet storage of HOL Light proof graphs

The stored objects are the original kernel requests and physical receipts.
Every request operand, type/source annotation, theorem hypothesis and axiom
tag, source origin, ordered parent occurrence and selected root is retained.
Binary indices have no machine-word bound. Decoding checked terms uses the
shared syntax codec; logical authorization remains with the original checker.
The serialization stages use executed finite-control list assembly and field
packing, with clocks attached to their original complete field bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ProofDataEncoding

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open SourceSubstitution
open ProofExecution

def typeMapletCodec : Codec (Ty × Ty) := Codec.prod tyCodec tyCodec
def termMapletCodec : Codec TermMaplet := Codec.prod checkedSourceCodec sourceTermCodec

def putInference : InferenceRequest → Data
  | .refl value => .pair (.atom 0) (canonicalCodec.put value)
  | .trans left right => .pair (.atom 1) (.pair (theoremCodec.put left) (theoremCodec.put right))
  | .mkComb left right => .pair (.atom 2) (.pair (theoremCodec.put left) (theoremCodec.put right))
  | .abs binder input => .pair (.atom 3) (.pair (sourceVarCodec.put binder) (theoremCodec.put input))
  | .beta value => .pair (.atom 4) (checkedSourceCodec.put value)
  | .assume value => .pair (.atom 5) (canonicalCodec.put value)
  | .eqMp left right => .pair (.atom 6) (.pair (theoremCodec.put left) (theoremCodec.put right))
  | .deductAntisym left right => .pair (.atom 7) (.pair (theoremCodec.put left) (theoremCodec.put right))
  | .instType entries input => .pair (.atom 8)
      (.pair ((Codec.list typeMapletCodec).put entries) (theoremCodec.put input))
  | .inst entries input => .pair (.atom 9)
      (.pair ((Codec.list termMapletCodec).put entries) (theoremCodec.put input))

def getInference : Data → Option InferenceRequest
  | .pair (.atom 0) value => (canonicalCodec.get value).map InferenceRequest.refl
  | .pair (.atom 1) (.pair left right) => do return .trans (← theoremCodec.get left) (← theoremCodec.get right)
  | .pair (.atom 2) (.pair left right) => do return .mkComb (← theoremCodec.get left) (← theoremCodec.get right)
  | .pair (.atom 3) (.pair binder input) => do return .abs (← sourceVarCodec.get binder) (← theoremCodec.get input)
  | .pair (.atom 4) value => (checkedSourceCodec.get value).map InferenceRequest.beta
  | .pair (.atom 5) value => (canonicalCodec.get value).map InferenceRequest.assume
  | .pair (.atom 6) (.pair left right) => do return .eqMp (← theoremCodec.get left) (← theoremCodec.get right)
  | .pair (.atom 7) (.pair left right) => do return .deductAntisym (← theoremCodec.get left) (← theoremCodec.get right)
  | .pair (.atom 8) (.pair entries input) => do
      return .instType (← (Codec.list typeMapletCodec).get entries) (← theoremCodec.get input)
  | .pair (.atom 9) (.pair entries input) => do
      return .inst (← (Codec.list termMapletCodec).get entries) (← theoremCodec.get input)
  | _ => none

theorem getInference_putInference (value : InferenceRequest) :
    getInference (putInference value) = some value := by
  cases value <;> simp [putInference, getInference, canonicalCodec.get_put, theoremCodec.get_put,
    sourceVarCodec.get_put, checkedSourceCodec.get_put,
    (Codec.list typeMapletCodec).get_put, (Codec.list termMapletCodec).get_put]

def inferenceCodec : Codec InferenceRequest := ⟨putInference, getInference, getInference_putInference⟩

def putRequest : RuleRequest → Data
  | .inference value => .pair (.atom 0) (putInference value)
  | .axiom value => .pair (.atom 1) (sequentCodec.put value)

def getRequest : Data → Option RuleRequest
  | .pair (.atom 0) value => (getInference value).map RuleRequest.inference
  | .pair (.atom 1) value => (sequentCodec.get value).map RuleRequest.axiom
  | _ => none

theorem getRequest_putRequest (value : RuleRequest) : getRequest (putRequest value) = some value := by
  cases value <;> simp [putRequest, getRequest, getInference_putInference, sequentCodec.get_put]

def requestCodec : Codec RuleRequest := ⟨putRequest, getRequest, getRequest_putRequest⟩
def originCodec : Codec Origin := Codec.prod Codec.string Codec.nat

def receiptCodec : Codec Receipt :=
  (Codec.prod theoremCodec (Codec.prod requestCodec (Codec.prod (Codec.list Codec.nat) originCodec))).mapped
    (fun value => (value.conclusion, value.witness, value.parents, value.origin))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩) (fun _ => rfl)

/-- The original list of physical graph occurrences and its selected root. -/
def certificateCodec : Codec ProofSystem.Certificate := Codec.prod (Codec.list receiptCodec) Codec.nat

def encodeCertificate (value : ProofSystem.Certificate) : List Alphabet := encodeWith certificateCodec value
def decodeCertificate (word : List Alphabet) : Option ProofSystem.Certificate := decodeWith certificateCodec word

theorem decodeCertificate_encodeCertificate (value : ProofSystem.Certificate) :
    decodeCertificate (encodeCertificate value) = some value := decodeWith_encodeWith certificateCodec value

theorem decodeCertificate_trailing_refused (value : ProofSystem.Certificate)
    (tail : List Alphabet) (nonempty : tail.isEmpty = false) :
    decodeCertificate (encodeCertificate value ++ tail) = none :=
  decodeWith_trailing_refused certificateCodec value tail nonempty

theorem encodeCertificate_injective : Function.Injective encodeCertificate := encodeWith_injective certificateCodec

/-- An actual finite-alphabet encoding of the original complete certificate. -/
def certificateEncoding : Computability.Encoding ProofSystem.Certificate Alphabet := encoding certificateCodec

private theorem smallTag (value : Nat) (small : value ≤ 9) :
    (Nat.digits 2 value).length ≤ 4 :=
  (Nat.digits_length_le_iff (by decide) value).mpr (by norm_num; omega)

theorem typeMaplet_payload_bound (value : Ty × Ty) :
    dataWeight (typeMapletCodec.put value) + 1 ≤ 64 * StorageSize.typeMaplet value := by
  have first := ty_payload_bound value.1
  have second := ty_payload_bound value.2
  change 1 + dataWeight (putTy value.1) + dataWeight (putTy value.2) + 1 ≤ _
  unfold StorageSize.typeMaplet
  omega

theorem termMaplet_payload_bound (value : TermMaplet) :
    dataWeight (termMapletCodec.put value) + 1 ≤ 64 * StorageSize.termMaplet value := by
  have first := checkedSource_payload_bound value.1
  have second := sourceTerm_payload_bound value.2
  change 1 + dataWeight (checkedSourceCodec.put value.1) + dataWeight (putSourceTerm value.2) + 1 ≤ _
  unfold StorageSize.termMaplet
  omega

theorem inference_payload_bound (value : InferenceRequest) :
    dataWeight (putInference value) + 1 ≤ 64 * StorageSize.inferenceRequest value := by
  cases value with
  | refl value =>
      have child := canonical_payload_bound value
      have tag := smallTag 0 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | trans left right =>
      have first := theorem_payload_bound left
      have second := theorem_payload_bound right
      have tag := smallTag 1 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | mkComb left right =>
      have first := theorem_payload_bound left
      have second := theorem_payload_bound right
      have tag := smallTag 2 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | abs binder input =>
      have first := sourceVar_payload_bound binder
      have second := theorem_payload_bound input
      have tag := smallTag 3 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | beta value =>
      have child := checkedSource_payload_bound value
      have tag := smallTag 4 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | assume value =>
      have child := canonical_payload_bound value
      have tag := smallTag 5 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | eqMp left right =>
      have first := theorem_payload_bound left
      have second := theorem_payload_bound right
      have tag := smallTag 6 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | deductAntisym left right =>
      have first := theorem_payload_bound left
      have second := theorem_payload_bound right
      have tag := smallTag 7 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest]
      omega
  | instType entries input =>
      have first := dataWeight_list_le typeMapletCodec StorageSize.typeMaplet 64 (by decide)
        typeMaplet_payload_bound entries
      have second := theorem_payload_bound input
      have tag := smallTag 8 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest, OpenTheory.StorageSize.list]
      omega
  | inst entries input =>
      have first := dataWeight_list_le termMapletCodec StorageSize.termMaplet 64 (by decide)
        termMaplet_payload_bound entries
      have second := theorem_payload_bound input
      have tag := smallTag 9 (by decide)
      simp only [putInference, dataWeight, StorageSize.inferenceRequest, OpenTheory.StorageSize.list]
      omega

theorem request_payload_bound (value : RuleRequest) :
    dataWeight (putRequest value) + 1 ≤ 64 * StorageSize.request value := by
  cases value with
  | inference value =>
      have child := inference_payload_bound value
      have tag := smallTag 0 (by decide)
      simp only [putRequest, dataWeight, StorageSize.request]
      omega
  | «axiom» value =>
      have child := sequent_payload_bound value
      have tag := smallTag 1 (by decide)
      simp only [putRequest, dataWeight, StorageSize.request]
      omega

theorem origin_payload_bound (value : Origin) :
    dataWeight (originCodec.put value) + 1 ≤ 64 * StorageSize.origin value := by
  have text := string_payload_bound value.1
  change 1 + dataWeight (Codec.string.put value.1) +
    (2 + (Nat.digits 2 value.2).length) + 1 ≤ _
  unfold StorageSize.origin OpenTheory.StorageSize.nat
  omega

private theorem digits_le_size (value : Nat) : (Nat.digits 2 value).length ≤ Nat.size value :=
  (Nat.digits_length_le_iff (by decide) value).mpr (Nat.lt_size_self value)

private theorem natural_payload_bound (value : Nat) :
    dataWeight (Codec.nat.put value) + 1 ≤ 64 * (1 + Nat.size value) := by
  have bound := digits_le_size value
  change 2 + (Nat.digits 2 value).length + 1 ≤ _
  omega

theorem receipt_payload_bound (value : Receipt) :
    dataWeight (receiptCodec.put value) + 1 ≤
      64 * (GraphExpansion.receiptWeight StorageSize.receiptPayload value +
        (value.parents.map Nat.size).sum) := by
  have conclusion := theorem_payload_bound value.conclusion
  have witness := request_payload_bound value.witness
  have provenance := origin_payload_bound value.origin
  have parents := dataWeight_list_le Codec.nat (fun n => 1 + Nat.size n) 64 (by decide)
    natural_payload_bound value.parents
  have indices : (value.parents.map (fun n => 1 + Nat.size n)).sum =
      value.parents.length + (value.parents.map Nat.size).sum := by
    induction value.parents with
    | nil => rfl
    | cons first rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  rw [indices] at parents
  change (1 + dataWeight (theoremCodec.put value.conclusion) +
    (1 + dataWeight (putRequest value.witness) +
      (1 + dataWeight ((Codec.list Codec.nat).put value.parents) +
        dataWeight (originCodec.put value.origin)))) + 1 ≤ _
  unfold GraphExpansion.receiptWeight StorageSize.receiptPayload
  omega

private theorem receipts_payload_bound (values : List Receipt) :
    dataWeight ((Codec.list receiptCodec).put values) ≤
      64 * (1 + GraphExpansion.binaryGraphWeight StorageSize.receiptPayload values) := by
  have bound := dataWeight_list_le receiptCodec
    (fun value => GraphExpansion.receiptWeight StorageSize.receiptPayload value +
      (value.parents.map Nat.size).sum) 64 (by decide) receipt_payload_bound values
  have sums : (values.map (fun value => GraphExpansion.receiptWeight StorageSize.receiptPayload value +
        (value.parents.map Nat.size).sum)).sum =
      GraphExpansion.binaryGraphWeight StorageSize.receiptPayload values := by
    clear bound
    induction values with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.map_cons, List.sum_cons, GraphExpansion.binaryGraphWeight,
          GraphExpansion.graphWeight, GraphExpansion.parentAddressBits] at *
        omega
  rw [sums] at bound
  exact bound

/-- Full stored graph payloads have a finite-alphabet representation bounded
by the independent structural account, including every binary address. -/
theorem certificate_payload_bound (value : ProofSystem.Certificate) :
    dataWeight (certificateCodec.put value) ≤ 64 * StorageSize.certificateUnits value := by
  have graph := receipts_payload_bound value.1
  change 1 + dataWeight ((Codec.list receiptCodec).put value.1) +
    (2 + (Nat.digits 2 value.2).length) ≤ _
  unfold StorageSize.certificateUnits OpenTheory.StorageSize.nat
  omega

theorem encodeCertificate_length (value : ProofSystem.Certificate) :
    (encodeCertificate value).length ≤ 64 * StorageSize.certificateUnits value := by
  simpa only [encodeCertificate, encodeWith, encodeData, writeData_length, List.length_nil,
    Nat.add_zero] using certificate_payload_bound value

/-- Three bits per physical alphabet symbol bound the actual representation.
This theorem concerns output size, not serialization or checker execution time. -/
theorem encodeCertificate_bit_bound (value : ProofSystem.Certificate) :
    3 * (encodeCertificate value).length ≤ 24 * StorageSize.certificateBits value := by
  have bound := encodeCertificate_length value
  unfold StorageSize.certificateBits
  omega

namespace Controls

theorem unknown_inference_refused : getInference (.pair (.atom 10) (.atom 0)) = none := rfl

theorem empty_word_refused : decodeCertificate [] = none := rfl

/-- Both physical premise occurrences are retained even when their address
is the same, and the source origin is retained with its full UTF-8 payload. -/
theorem receipt_roundtrip (conclusion : Theorem) (witness : RuleRequest) (parent : Nat) :
    decodeWith receiptCodec (encodeWith receiptCodec
      ⟨conclusion, witness, [parent, parent], ("証明🌿", parent)⟩) =
      some ⟨conclusion, witness, [parent, parent], ("証明🌿", parent)⟩ :=
  decodeWith_encodeWith receiptCodec _

end Controls

namespace Serialization

set_option backward.isDefEq.respectTransparency false
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming
open Mettapedia.Computability.WordTemplateMachine
open _root_.Computability Turing
open ProofExecution
attribute [local implicit_reducible] Indexed.machine Indexed.Alphabet

/-- The physical input retains every complete original receipt, including
ordered parents, full theorem/request data and original provenance. -/
def receiptInput (receipts : List Receipt) : List (Option Alphabet) :=
  framedArguments receiptCodec receipts

def receiptOutput (receipts : List Receipt) : List Alphabet :=
  1 :: encodeWith (Codec.list receiptCodec) receipts

/-- Actual list assembly counts complete receipt bytes and all framing cells. -/
def receiptOutputs (receipts : List Receipt) :
    TM2OutputsInTime ListAssembly.machine (receiptInput receipts)
      (some (receiptOutput receipts)) (3 * (receiptInput receipts).length + 4) := by
  rw [receiptInput, receiptOutput, ← ListAssembly.wire_codec]
  exact ListAssembly.outputs _

noncomputable def receiptRealization : TM2ComputableInPolyTime receiptInput receiptOutput id :=
  ListAssembly.realization receiptCodec

/-- Physical receipt packing retains four independently constructed original
fields. The template contributes only the existing nested product markers. -/
def nodeTemplate : Indexed.Template Alphabet 4 :=
  [.inl 4, .inr 0, .inl 4, .inr 1, .inl 4, .inr 2, .inr 3]

def nodeFields (node : Receipt) : Fin 4 → List Alphabet :=
  ![encodeWith theoremCodec node.conclusion, encodeWith requestCodec node.witness,
    encodeWith (Codec.list Codec.nat) node.parents, encodeWith originCodec node.origin]

def nodeInput (node : Receipt) : List (Option Alphabet) :=
  Indexed.argumentWire (nodeFields node)

theorem node_exact (node : Receipt) :
    Indexed.instantiate nodeTemplate (nodeFields node) = encodeWith receiptCodec node := by
  simp [Indexed.instantiate, nodeTemplate, nodeFields, receiptCodec, Codec.prod,
    Codec.mapped, encodeWith, encodeData_pair]

theorem nodeInput_length (node : Receipt) :
    (nodeInput node).length = (encodeWith receiptCodec node).length + 1 := by
  rw [← node_exact]
  simp [nodeInput, Indexed.argumentWire, Indexed.frame_length, Indexed.instantiate,
    nodeTemplate, nodeFields, List.finRange_succ]
  omega

def nodeOutputs (node : Receipt) :
    TM2OutputsInTime (Indexed.machine nodeTemplate) (nodeInput node)
      (some (encodeWith receiptCodec node)) (32 * ((nodeInput node).length + 1)) := by
  have ran := Indexed.outputs nodeTemplate (nodeFields node)
  have coefficient : 4 * (nodeTemplate.length + 1) = 32 := rfl
  rw [coefficient, node_exact] at ran
  exact ran

def nodeEncodedOutputs (node : Receipt) :
    TM2OutputsInTime (Indexed.machine nodeTemplate) (nodeInput node)
      (some (encodeWith receiptCodec node)) (32 * (encodeWith receiptCodec node).length + 64) := by
  have ran := nodeOutputs node
  have exactClock : 32 * ((nodeInput node).length + 1) =
      32 * (encodeWith receiptCodec node).length + 64 := by rw [nodeInput_length]; omega
  rw [exactClock] at ran
  exact ran

/-- Storage assembly cannot grant logical authority: it produces the same
original receipt that the independent kernel will subsequently check. -/
theorem node_decodes (node : Receipt) :
    decodeWith receiptCodec (Indexed.instantiate nodeTemplate (nodeFields node)) = some node := by
  rw [node_exact]
  exact decodeWith_encodeWith receiptCodec node

/-- A node's complete physical payload is charged inside its serialized graph.
Membership retains duplicate occurrences and does not forget provenance. -/
theorem nodeLength_le_certificate (certificate : ProofSystem.Certificate) (node : Receipt)
    (member : node ∈ certificate.1) :
    (encodeWith receiptCodec node).length ≤ (encodeCertificate certificate).length := by
  have inside := encodeWith_list_member_length receiptCodec certificate.1 node member
  change _ ≤ (encodeData (.pair ((Codec.list receiptCodec).put certificate.1)
    (Codec.nat.put certificate.2))).length
  rw [encodeData_pair]
  change _ ≤ (4 :: (encodeWith (Codec.list receiptCodec) certificate.1 ++
    encodeWith Codec.nat certificate.2)).length
  simp only [List.length_cons, List.length_append]
  omega

/-- Root packaging uses two dynamic original fields; neither field is placed
in finite control. The original product marker remains the only new byte. -/
def template : Indexed.Template Alphabet 2 := [.inl 4, .inr 0, .inr 1]

def fields (certificate : ProofSystem.Certificate) : Fin 2 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) certificate.1, encodeWith Codec.nat certificate.2]

def packageInput (certificate : ProofSystem.Certificate) : List (Option Alphabet) :=
  Indexed.argumentWire (fields certificate)

theorem package_exact (certificate : ProofSystem.Certificate) :
    Indexed.instantiate template (fields certificate) = encodeCertificate certificate := by
  simp only [Indexed.instantiate, template, List.flatMap_cons, List.flatMap_nil,
    List.singleton_append, List.append_nil, fields, Matrix.cons_val_zero]
  change 4 :: encodeWith (Codec.list receiptCodec) certificate.1 ++ encodeWith Codec.nat certificate.2 =
    encodeData (.pair ((Codec.list receiptCodec).put certificate.1) (.atom certificate.2))
  rw [encodeData_pair]
  rfl

/-- Packing executes the same indexed copier used by original term templates.
It preserves the selected root and every physical node occurrence. -/
def packageOutputs (certificate : ProofSystem.Certificate) :
    TM2OutputsInTime (Indexed.machine template) (packageInput certificate)
      (some (encodeCertificate certificate)) (16 * ((packageInput certificate).length + 1)) := by
  have ran := Indexed.outputs template (fields certificate)
  have coefficient : 4 * (template.length + 1) = 16 := rfl
  rw [coefficient, package_exact] at ran
  exact ran

/-- The packed target is decoded by the original lossless graph codec. -/
theorem package_decodes (certificate : ProofSystem.Certificate) :
    decodeCertificate (Indexed.instantiate template (fields certificate)) = some certificate := by
  rw [package_exact, decodeCertificate_encodeCertificate]

theorem packageInput_length (certificate : ProofSystem.Certificate) :
    (packageInput certificate).length = (encodeCertificate certificate).length + 1 := by
  simp only [packageInput, Indexed.argumentWire, Indexed.frame_length,
    List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil, fields, Matrix.cons_val_zero, Matrix.cons_val_succ]
  change _ = (encodeData (.pair ((Codec.list receiptCodec).put certificate.1) (.atom certificate.2))).length + 1
  rw [encodeData_pair]
  simp only [List.length_cons, List.length_append, encodeWith, Codec.nat]
  omega

/-- This is a clock for the packaging stage. Whole translation still has to
construct these two physical fields and compose all preceding operations. -/
def packageEncodedOutputs (certificate : ProofSystem.Certificate) :
    TM2OutputsInTime (Indexed.machine template) (packageInput certificate)
      (some (encodeCertificate certificate)) (16 * (encodeCertificate certificate).length + 32) := by
  have execution := packageOutputs certificate
  have exactClock : 16 * ((packageInput certificate).length + 1) =
      16 * (encodeCertificate certificate).length + 32 := by rw [packageInput_length]; omega
  rw [exactClock] at execution
  exact execution

end Serialization

end Mettapedia.Languages.HOLLight.ProofDataEncoding
