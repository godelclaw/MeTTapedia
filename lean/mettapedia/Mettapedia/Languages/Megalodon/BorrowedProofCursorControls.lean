import Mettapedia.Languages.Megalodon.BorrowedProofCursor

/-! # Context, ordered premises, selected theories and retained Megalodon cursors -/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.BorrowedProofCursor.Controls

open MathdataKernel ProofJudgment
open Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor
open Mettapedia.Machines
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Outcome)
open Mettapedia.Machines.Cursor.ProofChecking

private def p : MathdataKernel.Tm := .named "p"
private def q : MathdataKernel.Tm := .named "q"
private def environment : Environment :=
  { terms := [⟨"p", .prop, none⟩, ⟨"q", .prop, none⟩]
    known := [⟨"implication", .imp p q⟩, ⟨"premise", p⟩] }
private def emptyContext : Context := ⟨0, [], []⟩
private def workingContext : Context := ⟨0, [], [.imp p q, p]⟩
private def assumptionContext : Context := emptyContext.proofBinder p

private def source : Source := ⟨1, fun address => match address with
  | 10 => some ⟨⟨workingContext, .imp p q⟩, .hyp 0, [], 10⟩
  | 20 => some ⟨⟨workingContext, p⟩, .hyp 1, [], 20⟩
  | 30 => some ⟨⟨workingContext, q⟩, .proofApp p, [10, 20], 30⟩
  | 31 => some ⟨⟨workingContext, q⟩, .proofApp p, [20, 10], 31⟩
  | 40 => some ⟨⟨assumptionContext, p⟩, .hyp 0, [], 40⟩
  | 41 => some ⟨⟨workingContext, q⟩, .proofApp p, [10, 40], 41⟩
  | 50 => some ⟨⟨emptyContext, .imp p p⟩, .proofLam p, [40], 50⟩
  | 60 => some ⟨⟨emptyContext, q⟩, .hyp 0, [], 60⟩
  | 70 => some ⟨⟨⟨0, [.prop], []⟩, .typeAll p⟩, .typeLam, [20], 70⟩
  | 80 => some ⟨⟨emptyContext, p⟩, .known "premise", [], 80⟩
  | _ => none⟩

private def checked (env : Environment) (schedule : List Nat) (address : Nat) : Option Judgment := do
  let cursor ← (begin env 8 source).advance schedule
  pure (← cursor.root address).judgment

theorem native_modus_ponens : checked environment [10, 20, 30] 30 = some ⟨workingContext, q⟩ := by decide +kernel

/-- A stored known declaration is normalized by the real local checker. -/
theorem known_rule_accepted :
    requirements environment 8 (.known "premise") ⟨emptyContext, p⟩ = some [] := by
  simp [requirements, environment, p, q, MathdataKernel.normalize,
    deltaNormalize, Environment.lookupKnown?, lookupKnownList?, Environment.lookupTerm?,
    lookupTermList?, Tm.normalize, Tm.normalizeOne]

theorem ordered_parents_matter : checked environment [10, 20, 31] 31 = none := by decide +kernel
theorem assumption_is_not_global_theorem : checked environment [10, 40, 41] 41 = none := by decide +kernel
theorem discharge_requires_extended_context :
    requirements environment 8 (.proofLam p) ⟨emptyContext, .imp p p⟩ =
      some [⟨assumptionContext, p⟩] := by
  simp [requirements, environment, emptyContext, assumptionContext, Context.proofBinder,
    p, q, MathdataKernel.normalize, deltaNormalize, inferTerm, Environment.lookupTerm?,
    lookupTermList?, Tm.normalize, Tm.normalizeOne]

theorem no_hypothesis_in_empty_context : checked environment [60] 60 = none := by decide +kernel
theorem type_generalization_requires_empty_contexts : checked environment [20, 70] 70 = none := by decide +kernel
theorem profile_without_axiom_refuses :
    checked { environment with known := [⟨"implication", .imp p q⟩] } [80] 80 = none := by decide +kernel
theorem unchecked_future_parent_refused : checked environment [30, 10, 20] 30 = none := by decide +kernel

private def workerMachine := Mettapedia.Machines.Cursor.ProofChecking.machine (interface environment 8) source
private def work := start (begin environment 8 source) [10, 20, 30]

theorem resume_exact (first extra : Nat) :
    OutcomeRunner.run workerMachine (first + extra) work =
      OutcomeRunner.resume workerMachine extra (OutcomeRunner.run workerMachine first work) :=
  check_only_run_add _ _ first extra work

theorem pause_is_not_refusal : completedVerdict (OutcomeRunner.run workerMachine 1 work) = none := by decide +kernel
theorem whole_schedule_accepts : completedVerdict (OutcomeRunner.run workerMachine 5 work) = some true := by decide +kernel
theorem unused_bad_row_invalidates_batch :
    completedVerdict (OutcomeRunner.run workerMachine 6
      (start (begin environment 8 source) [10, 20, 30, 60])) = some false := by decide +kernel

private def retained (outcome : Outcome (Work (interface environment 8) source)
    (Report (interface environment 8) source) Empty) :
    Option (List Nat × Nat × Option Judgment) :=
  match outcome with
  | .exhausted work => some (work.pending, work.accepted, (work.cursor.root 30).map CheckedJudgment.judgment)
  | .finished report => some (report.work.pending, report.work.accepted,
      (report.work.cursor.root 30).map CheckedJudgment.judgment)
  | _ => none

theorem refusal_keeps_prefix_and_suffix :
    retained (OutcomeRunner.run workerMachine 6
      (start (begin environment 8 source) [10, 20, 30, 60, 20])) =
        some ([60, 20], 3, some ⟨workingContext, q⟩) := by decide +kernel

end Mettapedia.Languages.Megalodon.BorrowedProofCursor.Controls
