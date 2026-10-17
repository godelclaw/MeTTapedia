import Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt

/-!
# Positive and adversarial MM2 firing receipts

The selected directive matches a gate and two separately tagged facts carrying
the same payload. Its remove sink consumes the gate only after matching has
closed. Its add sink stores one payload atom, while the receipt must retain
both distinct input occurrences. The explicit rows below are expected data,
not outputs obtained by calling the checker or its matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MM2MatchingCursor (Row)
open MM2MatchingBatch.Controls (symbol term selfReader)
open WQComputable

def gate : Atom := term "gate" []
def seed (name : String) : Atom := term "seed" [symbol name, symbol "a"]
def output : Atom := term "out" [symbol "a"]

def activation : Atom := term "exec" [symbol "a",
  term "," [gate, term "seed" [.var "id", .var "x"]],
  term "O" [term "-" [gate], term "+" [term "out" [.var "x"]]]]

def source : List Atom := [activation, gate, seed "u", seed "v"]
def target : List Atom := [seed "u", seed "v", output]

def expectedRows : List Row := [
  ([("x", symbol "a"), ("id", symbol "u")], [(seed "u", 2), (gate, 1)]),
  ([("x", symbol "a"), ("id", symbol "v")], [(seed "v", 3), (gate, 1)])]

def receipt : Receipt := ⟨activation, 512, expectedRows⟩

theorem complete_occurrence_receipt_accepts : check source target receipt = true := by decide +kernel

theorem support_fragment_admitted : supportAdmissionB source = true := by decide +kernel

theorem accepted_receipt_is_an_original_source_step :
    (reflectiveSourceExecGSLT .leaveInert).Step source.toFinset target.toFinset :=
  (admitted_support_step_iff_receipt source target.toFinset support_fragment_admitted).mpr
    ⟨target, receipt, complete_occurrence_receipt_accepts, rfl⟩

theorem original_event_preserves_selected_activation :
    ∃ event : ReflectiveScheduledEvent source.toFinset target.toFinset,
      event.directive.atom = activation :=
  accepted_same_directive_event source target receipt
    (supportAdmissionB_invariant source support_fragment_admitted)
    complete_occurrence_receipt_accepts

theorem equal_outputs_still_require_both_inputs :
    receipt.rows.length = 2 ∧ target.count output = 1 := by decide +kernel

theorem single_success_is_not_complete :
    check source target { receipt with rows := expectedRows.take 1 } = false := by decide +kernel

theorem duplicated_first_witness_does_not_replace_second :
    check source target { receipt with rows := [expectedRows[0], expectedRows[0]] } = false := by decide +kernel

theorem forged_physical_position_refused :
    check source target { receipt with rows := [
      ([("x", symbol "a"), ("id", symbol "u")], [(seed "u", 3), (gate, 1)]),
      expectedRows[1]] } = false := by decide +kernel

theorem reversed_occurrence_order_refused :
    check source target { receipt with rows := expectedRows.reverse } = false := by decide +kernel

theorem premature_matcher_budget_refused :
    check source target { receipt with fuel := 1 } = false := by decide +kernel

theorem omitted_sink_update_refused :
    check source [seed "u", seed "v"] receipt = false := by decide +kernel

theorem removal_does_not_suppress_later_match :
    check source target receipt = true ∧ gate ∉ target ∧ receipt.rows.length = 2 := by decide +kernel

def laterActivation : Atom := term "exec" [symbol "b",
  term "," [gate, term "seed" [.var "id", .var "x"]],
  term "O" [term "-" [gate], term "+" [term "out" [.var "x"]]]]

theorem wrong_scheduled_directive_refused :
    check (laterActivation :: source) (laterActivation :: target)
      { receipt with directive := laterActivation } = false := by decide +kernel

def enlargedSource : List Atom := source ++ [seed "w"]
def enlargedTarget : List Atom := [seed "u", seed "v", seed "w", output]

def positiveReads (space : List Atom) (rows : List Row) : Bool :=
  rows.all (fun row => row.2.all (fun item => space[item.2]? == some item.1))

def selectedSnapshot (space : List Atom) : Option (List Atom) :=
  (selectNextScheduled (cSupportedSourceExecFacts space)).map (MM2MatchingBatch.snapshot space)

theorem snapshots_retain_the_selected_exec :
    selectedSnapshot source = some source ∧ selectedSnapshot enlargedSource = some enlargedSource := by decide +kernel

/-- Every positive witness is unchanged, but a new matching candidate changes
the closed enumeration. Snapshot identity cannot be reduced to those witnesses. -/
theorem positive_witnesses_survive_candidate_insertion :
    positiveReads source receipt.rows = true ∧ positiveReads enlargedSource receipt.rows = true := by decide +kernel

theorem candidate_insertion_invalidates_complete_receipt :
    check enlargedSource enlargedTarget receipt = false := by decide +kernel

theorem candidate_insertion_stays_in_admitted_fragment :
    supportAdmissionB enlargedSource = true := by decide +kernel

theorem repeated_physical_fact_is_not_a_set_snapshot :
    supportAdmissionB (source ++ [seed "u"]) = false := by decide +kernel

def alphaRenamedActivation : Atom := term "exec" [symbol "a",
  term "," [gate, term "seed" [.var "other-id", .var "other-x"]],
  term "O" [term "-" [gate], term "+" [term "out" [.var "other-x"]]]]

/-- Nominally distinct atoms can share a native compact key. Literal list
deduplication alone is insufficient for the support scheduler boundary. -/
theorem compact_key_collision_is_refused :
    activation ≠ alphaRenamedActivation ∧
      totalMorkCompactKey activation = totalMorkCompactKey alphaRenamedActivation ∧
      supportAdmissionB (alphaRenamedActivation :: source) = false := by decide +kernel

def headActivation : Atom := term "exec" [symbol "a", term "," [gate],
  term "O" [term "head" [symbol "1", output]]]

theorem extrema_needs_separate_support_correspondence :
    supportAdmissionB [headActivation, gate] = false := by decide +kernel

theorem absent_match_still_consumes_the_selected_exec :
    check [activation, gate] [gate] { receipt with rows := [] } = true := by decide +kernel

theorem missing_no_match_exhaustion_is_refused :
    check [activation, gate] [gate] { receipt with rows := [], fuel := 0 } = false := by decide +kernel

def selfReceipt : Receipt := ⟨selfReader, 512, [
  ([("output", term "," [term "read-self" []]),
    ("input", term "," [term "exec" [symbol "a", .var "input", .var "output"]])],
    [(selfReader, 0)])]⟩

theorem consumed_exec_is_still_readable_in_its_snapshot :
    check [selfReader] [term "read-self" []] selfReceipt = true := by decide +kernel

theorem pretending_exec_was_absent_from_snapshot_is_refused :
    check [selfReader] [term "read-self" []] { selfReceipt with rows := [] } = false := by decide +kernel

#print axioms complete_occurrence_receipt_accepts
#print axioms positive_witnesses_survive_candidate_insertion
#print axioms candidate_insertion_invalidates_complete_receipt
#print axioms consumed_exec_is_still_readable_in_its_snapshot
#print axioms accepted_receipt_is_an_original_source_step
#print axioms original_event_preserves_selected_activation
#print axioms compact_key_collision_is_refused

end Mettapedia.Languages.ProcessCalculi.MORK.MM2StepReceipt.Controls
