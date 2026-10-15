import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileBatches
import Mettapedia.OSLF.MeTTaIL.EquationOccurrenceNativeReceipts

/-!
# Resumable authored execution of the guarded binder profile

The queue consumes actual conditional-equation and directed-rule interpreter
batches. Its result retains the continuation, every conversion and every
primitive origin. The status distinguishes pending representative work from
unresolved admission. Closed runs also check their equation-walk certificate.
Semantic exhaustiveness is proved separately against the admitted profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderSearch

open Mettapedia.OSLF.MeTTaIL.Syntax Engine
open EquationFrontierBinderProfile
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

def model (ambient : Nat) (allowed : List Token) :=
  AuthoredEquationOccurrenceSearch.model (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc

def execute {ambient : Nat} (allowed : List Token) (fuel : Nat) (source : State ambient) :=
  run (model ambient allowed) fuel (initial source.pattern)

inductive Status where
  | searching (pendingCount : Nat)
  | unresolved (obligationCount : Nat)
  | certificateChecked
  | coverageRejected
  deriving DecidableEq, Repr

def status {ambient : Nat} (allowed : List Token) (fuel : Nat) (source : State ambient) : Status :=
  let snapshot := execute allowed fuel source
  if !snapshot.pending.isEmpty then .searching snapshot.pending.length
  else if !snapshot.parked.isEmpty then .unresolved snapshot.parked.length
  else if (Mettapedia.OSLF.Framework.ResumableEquationCoverage.coverageCertificate snapshot).check
      (Mettapedia.OSLF.Framework.ResumableEquationCoverage.equationNeighbors (model ambient allowed))
      source.pattern then .certificateChecked
  else .coverageRejected

theorem exact_resume {ambient : Nat} (allowed : List Token) (source : State ambient)
    (first second : Nat) :
    execute allowed (first + second) source =
      run (model ambient allowed) second (execute allowed first source) :=
  run_add (model ambient allowed) first second (initial source.pattern)

theorem preserves_complete_receipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (first second : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed first source).receipts) :
    receipt ∈ (execute allowed (first + second) source).receipts := by
  rw [exact_resume]
  exact run_preserves_receipt (model ambient allowed) second (execute allowed first source) receipt found

theorem partial_receipts_sound {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) :
    (execute allowed fuel source).Valid
      (AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc)
      (AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc) source.pattern :=
  AuthoredEquationOccurrenceSemantics.run_sound (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc source.pattern fuel

theorem checked_status_iff_quiescent {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) :
    status allowed fuel source = .certificateChecked ↔
      quiescent (execute allowed fuel source) = true := by
  have checked := Mettapedia.OSLF.Framework.ResumableEquationCoverage.quiescent_run_certificate_checked
    (model ambient allowed) source.pattern fuel
  unfold status
  dsimp only
  by_cases pending : (execute allowed fuel source).pending.isEmpty = true
  · by_cases parked : (execute allowed fuel source).parked.isEmpty = true
    · have quiet : quiescent (execute allowed fuel source) = true := by
        simp [quiescent, pending, parked]
      have passed := checked quiet
      simp only [execute] at pending parked passed quiet ⊢
      simp [pending, parked, passed, quiet]
    · simp [parked, pending, quiescent]
  · simp [pending, quiescent]

def nativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :=
  EquationOccurrenceNativeReceipts.emitted (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc source.pattern fuel receipt found

def sortedNativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :=
  EquationOccurrenceNativeReceipts.sortedNative (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc
    (nativeReceipt allowed source fuel receipt found)

theorem emitted_one_primitive_event {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    (EquationOccurrenceNativeReceipts.history (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc
      (nativeReceipt allowed source fuel receipt found)).length = 1 :=
  EquationOccurrenceNativeReceipts.history_primitive_count (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc _

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderSearch
