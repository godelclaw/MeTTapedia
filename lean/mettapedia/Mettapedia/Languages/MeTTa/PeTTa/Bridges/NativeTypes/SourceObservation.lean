import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.ReceiptCodec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution

/-! # Source-indexed observations of retained native execution

The transport retains the finite operational environment, source goal,
complete scheduler value, pending-work status and full receipt payloads.
Decoding is data recovery; provenance is supplied by the execution bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL CompleteExecution WireKit DescentCodec

abbrev Source := BindingPipeline.Installed.Source

/-- The finite names actually queried by a source and its fixed provider. -/
def footprint (environment : Environment) (source : Source) : List String :=
  providerFreeNames environment.provider ++ source.term.freeFvarNames

def environmentTerm (environment : Environment) (source : Source) : Term :=
  PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn (footprint environment source))

def sourceGoal (environment : Environment) (source : Source) : Scheduled.Goal :=
  Scheduled.sourceGoal environment source.bound source.type source.term

abbrev Snapshot (environment : Environment) (source : Source) :=
  Scheduled.Snapshot environment source.bound source.type source.term

structure Observation where
  environment : Term
  goal : Term
  snapshot : Term
  settled : Bool
  payloads : List Payload

def Observation.term (observation : Observation) : Term :=
  .application "NativeSourceReadout" [observation.environment, observation.goal,
    observation.snapshot, .symbol (if observation.settled then "NativeSettled" else "NativePending"),
    encodeList ReceiptCodec.encodePayload observation.payloads]

private def decodeBool? : Term → Option Bool
  | .symbol "NativeSettled" => some true
  | .symbol "NativePending" => some false
  | _ => none

def decodeObservation? : Term → Option Observation
  | .application "NativeSourceReadout" [environment, goal, snapshot, settled, payloads] => do
      pure ⟨environment, goal, snapshot, ← decodeBool? settled,
        ← decodeList ReceiptCodec.decodePayload? payloads⟩
  | _ => none

@[simp] theorem decodeObservation?_term (observation : Observation) :
    decodeObservation? observation.term = some observation := by
  cases observation with
  | mk environment goal snapshot settled payloads =>
    cases settled <;>
      simp [Observation.term, decodeObservation?, decodeBool?, decodeList_encodeList]

def decodeAtom? (atom : Atom) : Option Observation :=
  ReceiptCodec.decodeAtom? atom >>= decodeObservation?

@[simp] theorem decodeAtom?_encoded (observation : Observation) :
    decodeAtom? (encoded observation.term) = some observation := by
  simp [decodeAtom?, encoded]

def observe (environment : Environment) (source : Source) (snapshot : Snapshot environment source) :
    Observation :=
  ⟨environmentTerm environment source, goalTerm (sourceGoal environment source),
    stateTerm snapshot, snapshot.agenda.isEmpty,
    (Scheduled.receipts snapshot).map read⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution
