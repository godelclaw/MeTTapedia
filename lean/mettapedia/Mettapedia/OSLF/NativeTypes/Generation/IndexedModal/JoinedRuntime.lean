import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.CheckedFormation
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution

/-! # Runtime controls through one indexed-modal installation -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.JoinedRuntime

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.MeTTaIL.Syntax
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

def formationJudgment (installed : Joined.Installed) (index : installed.Index) : Judgment installed.symbols :=
  SignatureSum.judgmentLeft (SignatureSum.judgmentRight
    (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
      (installed.indexed.interfaces index)))
      (Declarations.modalCode (D := Pipeline.classifierSignature installed.indexed.operational)
        installed.indexed.interfaces index)
      (SignatureSum.typeLeft (result (D := Pipeline.classifierSignature installed.indexed.operational)
        (installed.indexed.interfaces index)))))

@[noinline] def checkOne (installed : Joined.Installed) (index : installed.Index) : IO Unit := do
  IO.eprintln ("Joined declaration " ++ toString index.val)
  let certificate := installed.formationCertificate index
  IO.eprintln "Formation table emitted"
  if installed.checkShared certificate (formationJudgment installed index) != .accepted then
    throw (IO.userError "Joined modal formation rejected")
  IO.eprintln "Formation table checked"
  if installed.checkShared (installed.focusCertificate index) (installed.focusJudgment index) != .accepted then
    throw (IO.userError "Joined focus classifier rejected")
  IO.eprintln "Focus table checked"
  if index.val = 0 then
    if installed.checkShared (installed.evidenceCertificate index) (installed.evidenceJudgment index) != .accepted then
      throw (IO.userError "Joined focus sort witness rejected")
  if installed.checkShared {certificate with root := certificate.rows.length} (formationJudgment installed index) == .accepted then
    throw (IO.userError "Out-of-range shared root accepted")

@[noinline] def formation (language : LanguageDef) : IO Unit := do
  IO.eprintln ("Joined generation " ++ language.name)
  let .ok installed := Consumers.generate language | throw (IO.userError "Joined language refused")
  IO.eprintln "Joined language installed"
  for index in List.finRange installed.indexed.headers.length do
    checkOne installed index
  IO.println (language.name ++ ": joined formation/focus checks=" ++ toString installed.indexed.headers.length)

def payloads (installed : Joined.Installed) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) : List Payload :=
  let source : BindingPipeline.Installed.Source := ⟨bound ambient, .base sort, pattern⟩
  let session := (BindingPipeline.Installed.CertifiedExecution.begin installed.indexed.operational source).resume budget
  session.receipts.map read

def checks (installed : Joined.Installed) (ambient : List String) (pattern : Pattern) (payload : Payload) : List Nat :=
  (List.finRange installed.indexed.headers.length).filterMap fun index =>
    if (installed.checkReceipt index ambient pattern payload).isSome then some index.val else none

@[noinline] def receipts (language : LanguageDef) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) : IO Unit := do
  let .ok installed := Consumers.generate language | throw (IO.userError "Joined language refused")
  let source : BindingPipeline.Installed.Source := ⟨bound ambient, .base sort, pattern⟩
  let paused := BindingPipeline.Installed.CertifiedExecution.begin installed.indexed.operational source
  if paused.absence != .unknown || paused.possibility (fun _ => true) != .unknown then
    throw (IO.userError "Incomplete initial state gave a verdict")
  let found := payloads installed ambient sort pattern budget
  if found.isEmpty then throw (IO.userError "No receipt discovered")
  for payload in found do
    if (checks installed ambient pattern payload).isEmpty then throw (IO.userError "Source receipt lost")
    if !(checks installed ambient pattern {payload with index := language.rewrites.length + 1}).isEmpty then
      throw (IO.userError "Invented source origin accepted")
    if payload.target != pattern && !(checks installed ambient pattern {payload with target := pattern}).isEmpty then
      throw (IO.userError "Invented target accepted")
    if !payload.captured.isEmpty && !(checks installed ambient pattern {payload with captured := []}).isEmpty then
      throw (IO.userError "Missing capture accepted")
    if !payload.history.isEmpty && !(checks installed ambient pattern {payload with history := []}).isEmpty then
      throw (IO.userError "Missing ordered premise history accepted")
    for index in List.finRange installed.indexed.headers.length do
      match installed.checkReceipt index ambient pattern payload with
      | none => pure ()
      | some receipt =>
        if read receipt.frame.point.val.receipt != payload then throw (IO.userError "Native receipt changed")
        for position in List.finRange installed.indexed.headers[index].indices.length do
          if !(SemanticReceipts.indexValue? installed.indexed installed.semantic index receipt.frame position).isSome then
            throw (IO.userError "Ordered index capture missing")
  IO.println (language.name ++ ": joined source/native receipts=" ++ toString found.length)

@[noinline] def binderFocus : IO Unit := do
  let .ok installed := Consumers.generate BindingPipeline.Controls.originalLambda
    | throw (IO.userError "Scoped lambda refused")
  let found := payloads installed [] "Term" Consumers.underBinderSource 2000
  let localFocus := found.any fun payload =>
    (List.finRange installed.indexed.headers.length).any fun index =>
      match installed.checkReceipt index [] Consumers.underBinderSource payload with
      | none => false
      | some receipt =>
        (installed.indexed.schema index).focusBound == [.base "Term"] &&
        (installed.indexed.interfaces index).focus.source == .base "Term" &&
        receipt.frame.focus != Consumers.underBinderSource && payload.target == Consumers.underBinderTarget
  if !localFocus then throw (IO.userError "Binder-local focus became a curried source classifier")
  IO.println "Binder control: raw Term focus retains its bound context"

@[noinline] def duplicateOrigins : IO Unit := do
  let .ok installed := Consumers.generate Consumers.sharedLanguage
    | throw (IO.userError "Shared-index language refused")
  let found := payloads installed [] "Program" Consumers.sharedSource 500
  if found.map (·.index) != [0, 1] || !found.all (fun payload => payload.target == Consumers.sharedTarget) then
    throw (IO.userError "Equal targets lost distinct authored origins")
  if !(payloads installed [] "Focus" Consumers.sharedSource 500).isEmpty then
    throw (IO.userError "Ill-sorted source admitted")
  for payload in found do
    let retainedIndex := (List.finRange installed.indexed.headers.length).any fun index =>
      match installed.checkReceipt index [] Consumers.sharedSource payload with
      | none => false
      | some receipt =>
        (List.finRange installed.indexed.headers[index].indices.length).any fun position =>
          match SemanticReceipts.indexValue? installed.indexed installed.semantic index receipt.frame position with
          | none => false
          | some value => value.val.body == .apply "F0" []
    if !retainedIndex then throw (IO.userError "Shared index value lost")
    if !(checks installed [] Consumers.sharedSource {payload with completed := []}).isEmpty then
      throw (IO.userError "Incomplete assignment accepted")
  IO.println "Duplicate-origin controls: equal targets retain ordered declarations 0 and 1"

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.JoinedRuntime
