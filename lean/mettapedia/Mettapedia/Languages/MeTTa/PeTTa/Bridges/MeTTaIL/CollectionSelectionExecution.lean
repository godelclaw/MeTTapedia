import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
import Mettapedia.OSLF.MeTTaIL.CollectionSelectionTrace

/-!
# Collection allocation source and execution

The source extends the shared scoped library. Its wire retains the selected
physical indices, explicit set retention, ordered selected values and residual.
This module's execution statements are against the Lean PeTTa semantics.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionSelectionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL.CollectionSelection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_selection.metta"
    sha256 "2c505e3b3b6241668e0c3f95d50ac1983666560234f4d03161d39e88dd659593"

/-- Only the scoped runtime source is needed below the collection allocator. -/
def scopedLibrary : BridgeKit.Library :=
  ⟨⟨[], [], [], [], []⟩, RuleExecutionProgram.scopedProgram, ["gslt:"]⟩

set_option maxRecDepth 100000 in
theorem scoped_checked : scopedLibrary.check = true := by decide +kernel

def library : BridgeKit.Library :=
  ⟨scopedLibrary.runtime, source.program, ["gslt:collection:"]⟩

set_option maxRecDepth 100000 in
theorem checked : library.check = true := by decide +kernel

def booleanTerm (value : Bool) : Term := .natural (if value then 1 else 0)

def decisionTerm (decision : Decision) : Term :=
  .application "CollectionDecision" [.natural decision.selected, booleanTerm decision.retained]

def choiceTerm {α : Type} (element : α → Term) (choice : Choice α) : Term :=
  .application "CollectionChoice"
    [.natural choice.selected, element choice.value, encodeList element choice.residual,
      booleanTerm choice.retained]

def allocationTerm {α : Type} (element : α → Term) (allocation : Allocation α) : Term :=
  .application "CollectionAllocation"
    [encodeList element allocation.values, encodeList element allocation.residual,
      encodeList decisionTerm allocation.decisions]

def pairTerm {α : Type} (element : α → Term) (pair : List α × List α) : Term :=
  .application "CollectionPair" [encodeList element pair.1, encodeList element pair.2]

syntax "collection_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        booleanTerm, decisionTerm, choiceTerm, allocationTerm, pairTerm, encodeList, encodeOption,
        $extra,*]))

theorem scoped_append_returns {α : Type} (element : α → Term) (state : State) :
    ∀ left right : List α,
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right)))
  | [], right => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList]
  | first :: rest, right => by
      metta_call scoped_checked
      metta_eval [scoped_append_returns element state rest right] with scoped_checked unfolding [encodeList]

theorem scoped_length_returns {α : Type} (element : α → Term) (state : State) :
    ∀ items : List α,
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length)
  | [] => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList]
  | first :: rest => by
      rw [show (first :: rest).length = 1 + rest.length by simp only [List.length_cons]; omega]
      metta_call scoped_checked
      metta_eval [scoped_length_returns element state rest] with scoped_checked unfolding [encodeList]

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : State)
    (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  metta_lift checked ["left", "right"] (scoped_append_returns element state left right)

/-- The existing physical eraser is reused; it never performs value-based
deletion that could merge equal bag occurrences. -/
theorem scoped_erase_returns {α : Type} (element : α → Term) (state : State) :
    ∀ (items : List α) (index : Nat),
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-match-erase-at" [number index, encoded (encodeList element items)])
      state (encoded (encodeList element (items.eraseIdx index)))
  | [], index => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList, List.eraseIdx_nil,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
  | value :: tail, 0 => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList, List.eraseIdx_zero,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]
  | value :: tail, index + 1 => by
      metta_call scoped_checked
      metta_eval [scoped_erase_returns element state tail index]
        with scoped_checked
        unfolding [encodeList, List.eraseIdx_cons_succ,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]

@[metta_head "gslt:rule:scope-match-erase-at"]
theorem erase_returns {α : Type} (element : α → Term) (state : State)
    (items : List α) (index : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-match-erase-at" [number index, encoded (encodeList element items)])
      state (encoded (encodeList element (items.eraseIdx index))) := by
  metta_lift checked ["index", "targets"] (scoped_erase_returns element state items index)

@[metta_head "gslt:collection:choices-from"]
theorem choices_from_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) (original : List α) : ∀ (items : List α) (index : Nat),
    PureReturns library.runtime [] state
      (apply "gslt:collection:choices-from"
        [encoded (booleanTerm idempotent), encoded (encodeList element original),
          encoded (encodeList element items), number index])
      state (encoded (encodeList (choiceTerm element)
        ((items.zipIdx index).flatMap fun (value, selected) =>
          let consumed : Choice α := ⟨selected, value, original.eraseIdx selected, false⟩
          if idempotent then [consumed, ⟨selected, value, original, true⟩] else [consumed])))
  | [], index => by
      collection_eval unfolding [List.zipIdx_nil, List.flatMap_nil]
  | value :: tail, index => by
      have erased := erase_returns element state original index
      have later := choices_from_returns element state idempotent original tail (index + 1)
      cases idempotent <;>
        collection_eval [erased, later] unfolding [List.zipIdx_cons, List.flatMap_cons]

@[metta_head "gslt:collection:choices"]
theorem choices_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:choices" [encoded (booleanTerm idempotent), encoded (encodeList element items)])
      state (encoded (encodeList (choiceTerm element) (choices idempotent items))) := by
  collection_eval [choices_from_returns element state idempotent items items 0]
    unfolding [choices]

@[metta_head "gslt:collection:prepend"]
theorem prepend_returns {α : Type} (element : α → Term) (state : State) (choice : Choice α) :
    ∀ allocations : List (Allocation α),
    PureReturns library.runtime [] state
      (apply "gslt:collection:prepend"
        [encoded (choiceTerm element choice), encoded (encodeList (allocationTerm element) allocations)])
      state (encoded (encodeList (allocationTerm element) (allocations.map (Allocation.prepend choice))))
  | [] => by
      cases choice
      collection_eval unfolding [List.map_nil]
  | allocation :: tail => by
      have later := prepend_returns element state choice tail
      cases choice
      cases allocation
      collection_eval [later] unfolding [List.map_cons, Allocation.prepend]

@[metta_head "gslt:collection:allocate-choices"]
theorem allocate_choices_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) (count : Nat)
    (children : ∀ items : List α,
      PureReturns library.runtime [] state
        (apply "gslt:collection:allocate"
          [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
        state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items)))) :
    ∀ selections : List (Choice α),
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate-choices"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList (choiceTerm element) selections)])
      state (encoded (encodeList (allocationTerm element)
        (selections.flatMap fun choice =>
          (tracedAllocations idempotent count choice.residual).map (Allocation.prepend choice))))
  | [] => by collection_eval unfolding [List.flatMap_nil]
  | choice :: tail => by
      have first := children choice.residual
      have prefixed := prepend_returns element state choice (tracedAllocations idempotent count choice.residual)
      have later := allocate_choices_returns element state idempotent count children tail
      have joined := append_returns (allocationTerm element) state
        ((tracedAllocations idempotent count choice.residual).map (Allocation.prepend choice))
        (tail.flatMap fun next =>
          (tracedAllocations idempotent count next.residual).map (Allocation.prepend next))
      cases choice
      collection_eval [first, prefixed, later, joined] unfolding [List.flatMap_cons]

/-- Executing the retained MeTTa source returns exactly the proved finite
allocator, including its complete index and retention history. -/
@[metta_head "gslt:collection:allocate"]
theorem allocate_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) : ∀ (count : Nat) (items : List α),
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
      state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items)))
  | 0, items => by collection_eval unfolding [tracedAllocations]
  | count + 1, items => by
      have selected := choices_returns element state idempotent items
      have children := allocate_choices_returns element state idempotent count
        (allocate_returns element state idempotent count) (choices idempotent items)
      collection_eval [selected, children] unfolding [tracedAllocations]

theorem scoped_row_returns {α : Type} (element : α → Term) (state : State) :
    ∀ (items : List α) (index : Nat),
    PureReturns scopedLibrary.runtime [] state
      (apply "gslt:rule:row-at" [number index, encoded (encodeList element items)])
      state (encoded (encodeOption element items[index]?))
  | [], index => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList, encodeOption, List.getElem?_nil]
  | value :: tail, 0 => by
      metta_call scoped_checked
      metta_eval unfolding [encodeList, encodeOption, List.getElem?_cons_zero]
  | value :: tail, index + 1 => by
      metta_call scoped_checked
      metta_eval [scoped_row_returns element state tail index]
        with scoped_checked
        unfolding [encodeList, encodeOption, List.getElem?_cons_succ,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]

@[metta_head "gslt:rule:row-at"]
theorem row_returns {α : Type} (element : α → Term) (state : State)
    (items : List α) (index : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:row-at" [number index, encoded (encodeList element items)])
      state (encoded (encodeOption element items[index]?)) := by
  metta_lift checked ["index", "rewrites"] (scoped_row_returns element state items index)

@[metta_head "gslt:collection:replay"]
theorem replay_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) : ∀ (decisions : List Decision) (items : List α),
    PureReturns library.runtime [] state
      (apply "gslt:collection:replay" [encoded (booleanTerm idempotent),
        encoded (encodeList element items), encoded (encodeList decisionTerm decisions)])
      state (encoded (encodeOption (pairTerm element) (replay idempotent items decisions)))
  | [], items => by collection_eval unfolding [replay]
  | decision :: tail, items => by
      have row := row_returns element state items decision.selected
      cases found : items[decision.selected]? with
      | none =>
          rw [found] at row
          cases decision
          collection_eval [row] unfolding [replay, found]
      | some value =>
          rw [found] at row
          have erased := erase_returns element state items decision.selected
          have consumed := replay_returns element state idempotent tail (items.eraseIdx decision.selected)
          have retained := replay_returns element state idempotent tail items
          rcases decision with ⟨index, kept⟩
          cases idempotent <;> cases kept
          · cases continued : replay false (items.eraseIdx index) tail with
            | none =>
                rw [continued] at consumed
                collection_eval [row, erased, consumed] unfolding [replay, found, continued]
            | some pair =>
                rcases pair with ⟨values, residual⟩
                rw [continued] at consumed
                collection_eval [row, erased, consumed] unfolding [replay, found, continued]
          · collection_eval [row] unfolding [replay, found]
          · cases continued : replay true (items.eraseIdx index) tail with
            | none =>
                rw [continued] at consumed
                collection_eval [row, erased, consumed] unfolding [replay, found, continued]
            | some pair =>
                rcases pair with ⟨values, residual⟩
                rw [continued] at consumed
                collection_eval [row, erased, consumed] unfolding [replay, found, continued]
          · cases continued : replay true items tail with
            | none =>
                rw [continued] at retained
                collection_eval [row, retained] unfolding [replay, found, continued]
            | some pair =>
                rcases pair with ⟨values, residual⟩
                rw [continued] at retained
                collection_eval [row, retained] unfolding [replay, found, continued]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionSelectionExecution
