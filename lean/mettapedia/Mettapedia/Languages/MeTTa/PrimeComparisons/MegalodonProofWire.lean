import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireData
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.RawInferenceService
import Mettapedia.Languages.Megalodon.IntrinsicProofChecker
import Mettapedia.Languages.Megalodon.NativeSyntaxWire

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

/-!
# Megalodon guest requests in the shared wire carrier

These codecs retain every constructor of the actual Mathdata types, terms
and proof objects, including constructors outside the Henkin soundness
fragment. Decoding is not formation or proof admission. The environment is
selected by the service, never supplied as an untrusted axiom table.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons
namespace MegalodonProofWire

open Mettapedia.Languages.Megalodon MathdataKernel NativeSyntaxWire

abbrev Wire := NativeWireData.Wire
abbrev Scope := RawInferenceService.Scope

/-- Every native judgment coordinate except the service's fixed environment. -/
structure Request where
  scope : Scope
  fuel : Nat
  typeDepth : Nat
  termContext : List Tp
  proofContext : List Tm
  proposition : Tm
  deriving DecidableEq, Repr

def Request.claim (request : Request) (environment : Environment) : IntrinsicProofChecker.Claim :=
  ⟨environment, request.fuel, request.typeDepth, request.termContext,
    request.proofContext, request.proposition⟩

def encodeRequest (request : Request) : Wire :=
  .application "NativeProof.request" [.natural request.scope.authority, .natural request.scope.revision,
    .natural request.fuel, .natural request.typeDepth,
    .application "types" (request.termContext.map encodeTp),
    .application "hypotheses" (request.proofContext.map encodeTm), encodeTm request.proposition]

def decodeRequest : Wire → Option Request
  | .application "NativeProof.request" [.natural authority, .natural revision,
      .natural fuel, .natural depth, .application "types" types,
      .application "hypotheses" hypotheses, proposition] => do
      return ⟨⟨authority, revision⟩, fuel, depth, ← decodeList decodeTp types,
        ← decodeList decodeTm hypotheses, ← decodeTm proposition⟩
  | _ => none

@[simp] theorem decodeRequest_encode (request : Request) :
    decodeRequest (encodeRequest request) = some request := by
  cases request
  simp only [encodeRequest, decodeRequest, decodeList_map encodeTp decodeTp decodeTp_encode,
    decodeList_map encodeTm decodeTm decodeTm_encode, decodeTm_encode]
  rfl

structure Packet where
  request : Request
  proof : Pf
  deriving DecidableEq, Repr

def encodePacket (packet : Packet) : Wire :=
  .application "NativeProof.packet" [encodeRequest packet.request, encodePf packet.proof]

def decodePacket : Wire → Option Packet
  | .application "NativeProof.packet" [request, proof] =>
      return ⟨← decodeRequest request, ← decodePf proof⟩
  | _ => none

@[simp] theorem decodePacket_encode (packet : Packet) :
    decodePacket (encodePacket packet) = some packet := by
  cases packet
  simp [decodePacket, encodePacket]

theorem encodePacket_injective : Function.Injective encodePacket := by
  intro first second same
  simpa only [decodePacket_encode, Option.some.injEq] using congrArg decodePacket same

theorem malformed_proof_rejected : decodePf (.application "Pf.proofApp" [.natural 0]) = none := rfl

/-- Successful serialization includes raw constructors not admitted by the
ordinary native checker. Codec coverage cannot serve as proof soundness. -/
theorem raw_gpa_retained (name : String) : decodePf (encodePf (.gpa name)) = some (.gpa name) :=
  decodePf_encode _

#print axioms decodeTp_encode
#print axioms decodeTm_encode
#print axioms decodePf_encode
#print axioms encodePf_injective
#print axioms decodeRequest_encode
#print axioms decodePacket_encode
#print axioms encodePacket_injective
#print axioms malformed_proof_rejected
#print axioms raw_gpa_retained

end MegalodonProofWire
end Mettapedia.Languages.MeTTa.PrimeComparisons
