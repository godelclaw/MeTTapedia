import Mettapedia.Languages.HOLLight.ChronologicalDriverCorrectness
import Mettapedia.GSLT.LanguageDef.CertificateProofTraversal

/-!
# Original binary storage for chronological controller tasks

The controller's existing task constructors and exact sites are serialized over
the original finite wire alphabet. Goals, proof bodies, rule instances, natural
indices and UTF-8 origins use their original codecs. This module supplies storage
and independent readout; physical task transitions are proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskEncoding

open ChronologicalDriver
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine

abbrev Alphabet := Binary.Alphabet

def originCodec : Codec ProofExecution.Origin :=
  Codec.prod Codec.string Codec.nat

def siteCodec : Codec Site :=
  (Codec.prod originCodec (Codec.list Codec.nat)).mapped
    (fun site => (site.origin, site.path))
    (fun pair => some ⟨pair.1, pair.2⟩) (fun _ => rfl)

def putTask : Task → Data
  | .visit goal proof site => .pair (.atom 0)
      (.pair (CertificateDataEncoding.patternCodec.put goal)
        (.pair (CertificateDataEncoding.proofCodec.put proof) (siteCodec.put site)))
  | .close goal ruleInstance premises site => .pair (.atom 1)
      (.pair (CertificateDataEncoding.patternCodec.put goal)
        (.pair (CertificateDataEncoding.instanceCodec.put ruleInstance)
          (.pair ((Codec.list CertificateDataEncoding.patternCodec).put premises) (siteCodec.put site))))
  | .save goal index => .pair (.atom 2)
      (.pair (CertificateDataEncoding.patternCodec.put goal) (Codec.nat.put index))
  | .finish goal => .pair (.atom 3) (CertificateDataEncoding.patternCodec.put goal)

def getTask : Data → Option Task
  | .pair (.atom 0) (.pair goal (.pair proof site)) => do
      return .visit (← CertificateDataEncoding.patternCodec.get goal)
        (← CertificateDataEncoding.proofCodec.get proof) (← siteCodec.get site)
  | .pair (.atom 1) (.pair goal (.pair ruleInstance (.pair premises site))) => do
      return .close (← CertificateDataEncoding.patternCodec.get goal)
        (← CertificateDataEncoding.instanceCodec.get ruleInstance)
        (← (Codec.list CertificateDataEncoding.patternCodec).get premises) (← siteCodec.get site)
  | .pair (.atom 2) (.pair goal index) => do
      return .save (← CertificateDataEncoding.patternCodec.get goal) (← Codec.nat.get index)
  | .pair (.atom 3) goal => do return .finish (← CertificateDataEncoding.patternCodec.get goal)
  | _ => none

theorem getTask_putTask (task : Task) : getTask (putTask task) = some task := by
  cases task <;> simp only [putTask, getTask, CertificateDataEncoding.patternCodec.get_put,
    CertificateDataEncoding.proofCodec.get_put, CertificateDataEncoding.instanceCodec.get_put,
    (Codec.list CertificateDataEncoding.patternCodec).get_put, siteCodec.get_put, Codec.nat.get_put]
  all_goals rfl

def taskCodec : Codec Task := ⟨putTask, getTask, getTask_putTask⟩
def workCodec : Codec (List Task) := Codec.list taskCodec

def encodeTask : Task → List Alphabet := encodeWith taskCodec
def decodeTask : List Alphabet → Option Task := decodeWith taskCodec

def encodeWork : List Task → List Alphabet := encodeWith workCodec
def decodeWork : List Alphabet → Option (List Task) := decodeWith workCodec

def encodeRoots : List Nat → List Alphabet := encodeWith (Codec.list Codec.nat)
def decodeRoots : List Alphabet → Option (List Nat) := decodeWith (Codec.list Codec.nat)

/-- Pending work, returned roots and chronological saved roots remain distinct
original lists. This wire packet carries addresses rather than erased proofs. -/
abbrev Packet := List Task × (List Nat × List Nat)
def packetCodec : Codec Packet := Codec.prod workCodec (Codec.prod (Codec.list Codec.nat) (Codec.list Codec.nat))
def encodePacket : Packet → List Alphabet := encodeWith packetCodec
def decodePacket : List Alphabet → Option Packet := decodeWith packetCodec

theorem decodeTask_encodeTask (task : Task) : decodeTask (encodeTask task) = some task :=
  decodeWith_encodeWith taskCodec task

theorem decodeWork_encodeWork (todo : List Task) : decodeWork (encodeWork todo) = some todo :=
  decodeWith_encodeWith workCodec todo

theorem decodePacket_encodePacket (packet : Packet) : decodePacket (encodePacket packet) = some packet :=
  decodeWith_encodeWith packetCodec packet

/-- Separators are outside the original byte alphabet; they do not reinterpret
or duplicate a task's original encoded payload. -/
def workStack (todo : List Task) : List (Option Alphabet) := Indexed.frame (todo.map encodeTask)

theorem workStack_cons (task : Task) (tail : List Task) :
    workStack (task :: tail) = (encodeTask task).map some ++ none :: workStack tail := by
  simp [workStack, Indexed.frame]

theorem workStack_append (first second : List Task) :
    workStack (first ++ second) = workStack first ++ workStack second := by
  simp [workStack, Indexed.frame]

/-- Actual proof visitation supplies original enter/reference/leave fields.
These structural events never confer semantic source admission. -/
abbrev proofEvents := CertificateProofTraversal.events

theorem original_reference_event (index : Nat) :
    CertificateProofTraversal.referenceWord index = CertificateDataEncoding.encodeProof (.premise index) := rfl

theorem task_visit_wire (goal : Pattern) (proof : RawOpenProof) (site : Site) :
    encodeTask (.visit goal proof site) =
      [4,3,2,4] ++ encodeWith CertificateDataEncoding.patternCodec goal ++
        [4] ++ CertificateDataEncoding.encodeProof proof ++ encodeWith siteCodec site := by
  simp only [encodeTask, encodeWith, taskCodec, putTask, encodeData_pair]
  simp only [CertificateDataEncoding.encodeProof, encodeWith]
  rw [show encodeData (.atom 0) = ([3,2] : List Alphabet) from rfl]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

end Mettapedia.Languages.HOLLight.ChronologicalTaskEncoding
