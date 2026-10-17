import Mettapedia.Languages.Megalodon.NativeSession

/-! # Native session acceptance, exhaustion, malformed rows and unfinished batches -/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeSession.Controls
open MathdataKernel ProofJudgment BorrowedProofCursor ObservedCursor
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

private def p : Tm := .named "p"
private def environment : Environment :=
  { terms := [⟨"p", .prop, none⟩, ⟨"alias", .prop, some p⟩]
    known := [⟨"proof", .named "alias"⟩] }
private def claim : Judgment := ⟨⟨0, [], []⟩, p⟩
private def source : Source := ⟨7, fun address => match address with
  | 10 => some ⟨claim, .known "proof", [], 10⟩
  | 20 => some ⟨claim, .hyp 0, [], 20⟩
  | _ => none⟩
private def afterTen : State Judgment := ⟨7, [(10, 0)], #[claim]⟩

theorem known_waits_for_conversion :
    observeStep environment 0 source (start source) 10 = .exhausted := by
  simp [observeStep, source, start, indexAt, premiseValues, RuleObservation.observe,
    environment, MathdataKernel.normalize, deltaNormalize, Environment.lookupKnown?, lookupKnownList?,
    Environment.lookupTerm?, lookupTermList?]

theorem known_accepts_on_retry :
    observeStep environment 1 source (start source) 10 = .accepted afterTen := by
  simp [observeStep, source, start, indexAt, premiseValues, RuleObservation.observe,
    environment, claim, p, afterTen, MathdataKernel.normalize, deltaNormalize,
    Environment.lookupKnown?, lookupKnownList?, Environment.lookupTerm?, lookupTermList?,
    Tm.normalize, Tm.normalizeOne]

theorem exhausted_retains_entire_suffix :
    walk environment 0 source 2 (start source) [10, 20] =
      ⟨.exhausted, start source, [10, 20]⟩ := by simp [walk, known_waits_for_conversion]

theorem row_budget_pauses_without_refuting :
    walk environment 1 source 1 (start source) [10, 20] = ⟨.paused, afterTen, [20]⟩ := by
  simp [walk, known_accepts_on_retry]

theorem invalid_row_retains_accepted_root :
    walk environment 1 source 2 (start source) [10, 20] = ⟨.refused, afterTen, [20]⟩ := by
  rw [walk, known_accepts_on_retry]
  simp [walk, observeStep, source, afterTen, indexAt, premiseValues, RuleObservation.observe, claim]

theorem malformed_address_retains_accepted_root :
    walk environment 1 source 2 (start source) [10, 99] = ⟨.malformed, afterTen, [99]⟩ := by
  rw [walk, known_accepts_on_retry]
  simp [walk, observeStep, source, afterTen, indexAt]

theorem duplicate_schedule_is_malformed :
    observeStep environment 1 source afterTen 10 = .malformed := by decide

theorem finished_batch_retains_root :
    walk environment 1 source 1 (start source) [10] = ⟨.finished, afterTen, []⟩ := by
  simp [walk, known_accepts_on_retry]

theorem closed_theorem_published :
    (finish (resume (begin environment source) 1 1 [10]) 10 1 p).isAccepted = true := by
  apply (finish_accepts_iff _ _ _ _).mpr
  refine ⟨?_, ?_, claim, ?_, rfl, ?_, ?_⟩
  · simp [resume, begin, finished_batch_retains_root]
  · simp [resume, begin, finished_batch_retains_root]
  · simp [resume, begin, finished_batch_retains_root, rootAt, afterTen, indexAt]
  · decide
  · simp [MathdataKernel.normalize, deltaNormalize, environment, p, claim,
      Environment.lookupTerm?, lookupTermList?, Tm.normalize, Tm.normalizeOne]

theorem successful_root_cannot_mask_later_failure :
    finish (resume (begin environment source) 1 2 [10, 20]) 10 1 p = .unfinished .refused := by
  simp [finish, resume, begin, invalid_row_retains_accepted_root]

theorem paused_batch_cannot_publish :
    finish (resume (begin environment source) 1 1 [10, 20]) 10 1 p = .unfinished .paused := by
  simp [finish, resume, begin, row_budget_pauses_without_refuting]

theorem wire_decoder_has_no_authority_backdoor :
    (sourceOfWire 7 (fun _ => some (.application "Sealed" [.string "proof"]))).read 10 = none := rfl

end Mettapedia.Languages.Megalodon.NativeSession.Controls
