import Mettapedia.Machines.ExecutionControl
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Planned case entry and indexed selection

The operand reader enters the maintained source machine's case continuation.
An independent bounded array scan agrees with its first-matching-row selector,
including the selected bindings and body. The scan receives prepared patterns;
pattern evaluation, the native Empty-default extension, source charging and C
pointer ownership retain their separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceCase

open Mettapedia.Languages.MeTTa.PeTTa
abbrev Atom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
abbrev Bindings := Mettapedia.Languages.ProcessCalculi.MORK.Subst

def enter (bindings : Bindings) (plan : ExecutionControl.Plan) (fields : Array Atom)
    (before : Eval.Configuration) : Option Eval.Configuration := do
  let .matchBranches key (.expression rows) ← ExecutionControl.read plan fields | none
  let cases ← Eval.readCases rows
  return {before with
    control := .evaluate bindings key
    frames := .select bindings cases :: before.frames}

theorem source_entry (program : SpaceSemantics.Program) (bindings : Bindings)
    (key : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases) (before : Eval.Configuration) :
    (ExecutionControl.elaborate .matchBranches 2).bind
        (fun plan => enter bindings plan #[key, .expression rows] before) =
      Eval.step program {before with
        control := .evaluate bindings (.expression [.symbol "case", key, .expression rows])} := by
  change (Eval.readCases rows).bind (fun parsed => some {before with
    control := .evaluate bindings key
    frames := .select bindings parsed :: before.frames}) = _
  simp [Eval.step, decoded]

theorem source_entry_derivation (program : SpaceSemantics.Program) (bindings : Bindings)
    (key : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (decoded : Eval.readCases rows = some cases) (before : Eval.Configuration) :
    DeclarativeSpec.Transition program
      {before with
        control := .evaluate bindings (.expression [.symbol "case", key, .expression rows])}
      {before with
        control := .evaluate bindings key
        frames := .select bindings cases :: before.frames} := by
  exact .case_enter rfl decoded

theorem storage_normalization (bindings : Bindings) (key arms : Atom)
    (before : Eval.Configuration) :
    enter bindings ⟨.matchBranches, some 1, some 0, none⟩ #[arms, key] before =
      enter bindings ⟨.matchBranches, some 0, some 1, none⟩ #[key, arms] before := by
  rfl

theorem missing_arms_refuses (bindings : Bindings) (fields : Array Atom)
    (before : Eval.Configuration) :
    enter bindings ⟨.matchBranches, some 0, none, none⟩ fields before = none := by
  simp [enter, ExecutionControl.matchBranches_missing_arms]

/-- `fuel` is a termination bound, supplied as the row count by the lowering;
it is independent of evaluator source fuel and physical execution slices. -/
def scan (bindings : Bindings) (key : Atom) (rows : Array (Atom × Atom)) :
    Nat → Nat → Option (Bindings × Atom)
  | 0, _ => none
  | fuel + 1, position =>
      if inside : position < rows.size then
        let (pattern, body) := rows[position]
        match SpaceSemantics.matchValue bindings pattern key with
        | some bound => some (bound, body)
        | none => scan bindings key rows fuel (position + 1)
      else none

/-- The array loop is compared to the independent source list selector.
Every failed trial reuses the original bindings, rather than a partial match. -/
theorem scan_refines (bindings : Bindings) (key : Atom) (rows : Array (Atom × Atom))
    (fuel position : Nat) (enough : rows.size ≤ position + fuel) :
    scan bindings key rows fuel position =
      SpaceSemantics.selectCase bindings key (rows.toList.drop position) := by
  induction fuel generalizing position with
  | zero =>
      have empty : rows.toList.drop position = [] :=
        List.drop_eq_nil_of_le (by simpa using enough)
      simp [scan, empty, SpaceSemantics.selectCase]
  | succ fuel ih =>
      by_cases inside : position < rows.size
      · rw [List.drop_eq_getElem_cons (by simpa using inside)]
        simp only [Array.getElem_toList]
        rcases row : rows[position] with ⟨pattern, body⟩
        cases matched : SpaceSemantics.matchValue bindings pattern key with
        | none =>
            simpa [scan, inside, row, SpaceSemantics.selectCase, matched] using
              ih (position + 1) (by omega)
        | some bound =>
            simp [scan, inside, row, SpaceSemantics.selectCase, matched]
      · have empty : rows.toList.drop position = [] :=
          List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt inside)
        simp [scan, inside, empty, SpaceSemantics.selectCase]

theorem compiled_rows_refine (bindings : Bindings) (key : Atom)
    (cases : SpaceSemantics.Cases) :
    scan bindings key cases.toArray cases.length 0 =
      SpaceSemantics.selectCase bindings key cases := by
  simpa using scan_refines bindings key cases.toArray cases.length 0 (by simp)

theorem selected_derivation (bindings bound : Bindings) (key body : Atom)
    (cases : SpaceSemantics.Cases)
    (selected : scan bindings key cases.toArray cases.length 0 = some (bound, body)) :
    SpaceSemantics.Selected bindings key cases bound body := by
  exact SpaceSemantics.selectCase_sound ((compiled_rows_refine bindings key cases).symm.trans selected)

def lowerReady {Value Effect Fault Delay Suspension : Type}
    (bindings : Bindings) (key : Atom) (cases : SpaceSemantics.Cases) :
    ContextualCBPV.Code Value (Bindings × Atom) Effect Fault Delay Suspension :=
  match scan bindings key cases.toArray cases.length 0 with
  | none => .failure
  | some selected => .invoke selected

def sourceReady {Value Effect Fault Delay Suspension : Type}
    (bindings : Bindings) (key : Atom) (cases : SpaceSemantics.Cases) :
    ContextualCBPV.Code Value (Bindings × Atom) Effect Fault Delay Suspension :=
  match SpaceSemantics.selectCase bindings key cases with
  | none => .failure
  | some (bound, body) => .invoke (bound, body)

theorem ready_refines {Value Effect Fault Delay Suspension : Type}
    (bindings : Bindings) (key : Atom) (cases : SpaceSemantics.Cases) :
    lowerReady (Value := Value) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension) bindings key cases =
      sourceReady bindings key cases := by
  simp only [lowerReady, sourceReady, compiled_rows_refine]
  cases SpaceSemantics.selectCase bindings key cases with
  | none => rfl
  | some selected => cases selected; rfl

/-- Complete indexed selection preserves the metered continuation, pending
alternatives and effects for every later slice, not just a final answer. -/
theorem metered_residual_refines {Value Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value (Bindings × Atom) Effect Fault Delay Suspension
      Context World Worker)
    (state : ContextualCBPV.State Value (Bindings × Atom) Effect Fault Delay Suspension
      Context World Worker)
    (context : Context) (bindings : Bindings) (key : Atom) (cases : SpaceSemantics.Cases)
    (occurrence debit sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (.source occurrence debit (lowerReady bindings key cases)), state.focus.frames⟩}, sourceFuel⟩ =
      machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context
          (.source occurrence debit (sourceReady bindings key cases)), state.focus.frames⟩}, sourceFuel⟩ := by
  simp only [ready_refines]

theorem first_match_wins :
    (scan [] (.symbol "key")
      #[(.var "x", .symbol "first"), (.var "y", .symbol "later")] 2 0).map Prod.snd =
      some (.symbol "first") := by
  decide +kernel

theorem skipping_first_match_changes_result :
    (scan [] (.symbol "key")
      #[(.var "x", .symbol "first"), (.var "y", .symbol "later")] 2 1).map Prod.snd ≠
      some (.symbol "first") := by
  decide +kernel

theorem selection_keeps_body_pending :
    (scan [] (.symbol "key")
      #[(.var "x", .expression [.symbol "empty"])] 1 0).map Prod.snd =
      some (.expression [.symbol "empty"]) := by
  decide +kernel

end Mettapedia.Machines.SourceCase

#print axioms Mettapedia.Machines.SourceCase.source_entry
#print axioms Mettapedia.Machines.SourceCase.source_entry_derivation
#print axioms Mettapedia.Machines.SourceCase.storage_normalization
#print axioms Mettapedia.Machines.SourceCase.missing_arms_refuses
#print axioms Mettapedia.Machines.SourceCase.scan_refines
#print axioms Mettapedia.Machines.SourceCase.compiled_rows_refine
#print axioms Mettapedia.Machines.SourceCase.selected_derivation
#print axioms Mettapedia.Machines.SourceCase.ready_refines
#print axioms Mettapedia.Machines.SourceCase.metered_residual_refines
#print axioms Mettapedia.Machines.SourceCase.first_match_wins
#print axioms Mettapedia.Machines.SourceCase.skipping_first_match_changes_result
#print axioms Mettapedia.Machines.SourceCase.selection_keeps_body_pending
