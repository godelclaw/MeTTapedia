import Mettapedia.OSLF.NativeTypes.Instances.Rho.ScheduledControls
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

open Mettapedia.OSLF.Framework

/-!
# Recorded decisions on the original rho scheduler

These executable controls retain the first conclusive horizon and the
receipt prefix at that horizon. The original budgets 80 and 90 exercise
early stopping on COMM and complete absence on constructor contexts.
The horizon is not an aggregate CPU or memory bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.Benchmark

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded
open Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.Controls

structure Snapshot where
  horizon : Nat
  answer : Option Bool
  receiptCount : Nat
  closed : Bool
  deriving Repr, BEq

def recorded (raw : Pattern) (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formula : Formula Empty) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded.run backend tests formula (originalSource raw accepted) budget

def snapshot (raw : Pattern) (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formula : Formula Empty) (budget : Nat) : Snapshot :=
  let record := recorded raw accepted formula budget
  let view := frontierView backend record
  ⟨record.horizon, record.outcome.answer, view.receipts.length, view.closed⟩

def snapshotRaw (formula : Formula Empty) (budget : Nat) (raw : Pattern) : Option Snapshot :=
  if accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true then
    some (snapshot raw accepted formula budget)
  else none

#guard snapshotRaw (.possibility .top) 0 redex == some ⟨0, none, 0, false⟩
#guard snapshotRaw (.possibility .top) 35 redex == some ⟨35, none, 0, false⟩
#guard snapshotRaw (.possibility .top) 80 redex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.possibility .top) 90 redex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.outgoingUniversal .bottom) 90 redex == some ⟨36, some false, 1, false⟩
#guard snapshotRaw (.possibility .bottom) 90 redex == some ⟨50, some false, 1, true⟩
#guard snapshotRaw (.outgoingUniversal .top) 90 redex == some ⟨50, some true, 1, true⟩
#guard snapshotRaw (.possibility (.possibility .top)) 90 redex == some ⟨50, some false, 1, true⟩
#guard snapshotRaw (.possibility .top) 80 parallelRedex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.possibility .top) 90 equivalentChannelRedex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.possibility .top) 90 reflectiveRedex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.possibility .top) 0 payloadRedex == some ⟨0, none, 0, false⟩
#guard snapshotRaw (.possibility .top) 80 payloadRedex == some ⟨2, some false, 0, true⟩
#guard snapshotRaw (.possibility .top) 80 guardedRedex == some ⟨2, some false, 0, true⟩
#guard snapshotRaw (.possibility .top) 90 quotedRedex == some ⟨2, some false, 0, true⟩
#guard snapshotRaw (.possibility .top) 80 stuckOutput == some ⟨2, some false, 0, true⟩
#guard snapshotRaw (.possibility .top) 90 stuckOutput == some ⟨2, some false, 0, true⟩
#guard snapshotRaw (.outgoingUniversal .bottom) 90 stuckOutput == some ⟨2, some true, 0, true⟩
#guard snapshotRaw (.possibility .top) 90 duplicateRedex == some ⟨36, some true, 1, false⟩
#guard snapshotRaw (.possibility .top) 90 (.apply "POutput" [zero, zero]) == none

/-- The four constructor nodes are the output, quote and two zeros. -/
theorem four_node_output_shape :
    stuckOutput = .apply "POutput"
      [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []] := rfl

theorem actual_horizon_is_bounded (raw : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formula : Formula Empty) (budget : Nat) :
    (recorded raw accepted formula budget).horizon ≤ budget :=
  run_horizon_le backend tests formula (originalSource raw accepted) budget

theorem actual_horizon_is_conclusive (raw : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formula : Formula Empty) (budget : Nat) (answer : Bool)
    (decided : (recorded raw accepted formula budget).outcome.answer = some answer) :
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw backend tests (recorded raw accepted formula budget).horizon formula
      (originalSource raw accepted)).answer = some answer :=
  run_stopped_at_answer backend tests formula (originalSource raw accepted) budget answer decided

theorem earlier_horizons_are_unknown (source : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source = true)
    (formula : Formula Empty) (budget previous : Nat)
    (positive : 1 ≤ previous)
    (earlier : previous < (recorded source accepted formula budget).horizon) :
    (raw backend tests previous formula (originalSource source accepted)).answer = none :=
  scan_prior_unknown _ 1 budget previous positive earlier

theorem recorded_native_positive (source : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source = true)
    (formula : Formula Empty) (budget : Nat)
    (decided : (recorded source accepted formula budget).outcome.answer = some true) :
    denotation tests formula (originalSource source accepted) :=
  (recorded source accepted formula budget).outcome.positive decided

theorem recorded_native_negative (source : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source = true)
    (formula : Formula Empty) (budget : Nat)
    (decided : (recorded source accepted formula budget).outcome.answer = some false) :
    ¬ denotation tests formula (originalSource source accepted) :=
  (recorded source accepted formula budget).outcome.negative decided

theorem retained_receipts_are_original_steps (source : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source = true)
    (formula : Formula Empty) (budget : Nat)
    (receipt : backend.Receipt (originalSource source accepted))
    (listed : receipt ∈ (frontierView backend (recorded source accepted formula budget)).receipts) :
    rhoReflectiveGSLT.Step (originalSource source accepted)
      (backend.target (originalSource source accepted) receipt) :=
  view_receipts_sound _ receipt listed

theorem closed_view_covers_original_steps (source : Pattern)
    (accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source = true)
    (formula : Formula Empty) (budget : Nat)
    (complete : (frontierView backend (recorded source accepted formula budget)).closed = true)
    (target : rhoReflectiveGSLT.Term) (step : rhoReflectiveGSLT.Step (originalSource source accepted) target) :
    ∃ receipt, receipt ∈ (frontierView backend (recorded source accepted formula budget)).receipts ∧
      rhoReflectiveGSLT.Equiv target (backend.target (originalSource source accepted) receipt) :=
  view_coverage _ complete target step

def rows : List (String × Nat × Option Snapshot) :=
  [("root COMM", 80, snapshotRaw (.possibility .top) 80 redex),
   ("root COMM", 90, snapshotRaw (.possibility .top) 90 redex),
   ("parallel COMM", 80, snapshotRaw (.possibility .top) 80 parallelRedex),
   ("equivalent names", 90, snapshotRaw (.possibility .top) 90 equivalentChannelRedex),
   ("reflective payload", 90, snapshotRaw (.possibility .top) 90 reflectiveRedex),
   ("nested possibility", 90, snapshotRaw (.possibility (.possibility .top)) 90 redex),
   ("output payload", 80, snapshotRaw (.possibility .top) 80 payloadRedex),
   ("input guard", 80, snapshotRaw (.possibility .top) 80 guardedRedex),
   ("quoted process", 90, snapshotRaw (.possibility .top) 90 quotedRedex),
   ("four-node output", 80, snapshotRaw (.possibility .top) 80 stuckOutput),
   ("four-node output", 90, snapshotRaw (.possibility .top) 90 stuckOutput),
   ("duplicate origins", 90, snapshotRaw (.possibility .top) 90 duplicateRedex),
   ("universal counterexample", 90, snapshotRaw (.outgoingUniversal .bottom) 90 redex),
   ("universal coverage", 90, snapshotRaw (.outgoingUniversal .top) 90 redex),
   ("complete absence", 90, snapshotRaw (.possibility .bottom) 90 redex)]

#eval rows

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.Benchmark
