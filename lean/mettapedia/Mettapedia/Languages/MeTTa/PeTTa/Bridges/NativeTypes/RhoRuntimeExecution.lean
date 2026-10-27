import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner

/-! # The target-side receipt tests compute the Lean query readout -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
open Eval BridgeKit

syntax "rho_native_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| rho_native_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call helpers_checked; metta_eval [$facts,*] with helpers_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, pattern_symbol_unmatched, $extra,*]))

theorem target_in_helper_returns (state : Effects.State)
    (receipt : GeneralOccurrenceSemantics.Receipt)
    (checked : Complete.Classes.Checked spec.plan spec.bound spec.expected receipt.target) :
    PureReturns helperLibrary.runtime [] state
      (apply "gslt:runner:target" [CompleteExecution.classSearchBackend, standardAtom spec, encoded (classReceiptTerm receipt)]) state
      (patternValue (committed receipt.target)) := by
  exact Library.lift_call helpers_checked (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["backend", "standard", "receipt"]
    (by decide) (by rfl) (by decide +kernel)
    (runner_target_returns spec.plan state spec.mode (table spec) (table_for spec)
      spec.bound spec.expected receipt checked)

private theorem hit_nil_returns (state : Effects.State) (standard : Term) (target : Pattern) :
    PureReturns helperLibrary.runtime [] state
      (apply "rho:native:hit" [encoded standard, patternValue target, .symbol "LNil"])
      state (Effects.boolean false) := by rho_native_eval

set_option maxHeartbeats 4000000 in
private theorem hit_cons_hit_returns (state : Effects.State) (standard receipt : Term)
    (rest : List Term) (target reached : Pattern)
    (here : PureReturns helperLibrary.runtime [] state
      (apply "gslt:runner:target" [CompleteExecution.classSearchBackend, encoded standard, encoded receipt]) state (patternValue reached))
    (same : reached = target) :
    PureReturns helperLibrary.runtime [] state
      (apply "rho:native:hit" [encoded standard, patternValue target,
        encoded (encodeList id (receipt :: rest))]) state (Effects.boolean true) := by
  subst reached
  rho_native_eval [here] unfolding [encodeList]

set_option maxHeartbeats 4000000 in
private theorem hit_cons_miss_returns (state : Effects.State) (standard receipt : Term)
    (rest : List Term) (target reached : Pattern) (result : Bool)
    (here : PureReturns helperLibrary.runtime [] state
      (apply "gslt:runner:target" [CompleteExecution.classSearchBackend, encoded standard, encoded receipt]) state (patternValue reached))
    (different : reached ≠ target)
    (later : PureReturns helperLibrary.runtime [] state
      (apply "rho:native:hit" [encoded standard, patternValue target, encoded (encodeList id rest)])
      state (Effects.boolean result)) :
    PureReturns helperLibrary.runtime [] state
      (apply "rho:native:hit" [encoded standard, patternValue target,
        encoded (encodeList id (receipt :: rest))]) state (Effects.boolean result) := by
  have encoded_ne : InferenceCettaWire.encodePattern reached ≠ InferenceCettaWire.encodePattern target :=
    fun equal => different (InferenceCettaWire.encodePattern_injective equal)
  rho_native_eval [here] unfolding [encodeList]
  all_goals
    rw [if_neg encoded_ne]
    metta_eval [later] with helpers_checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]

private theorem encode_receipts (receipts : List GeneralOccurrenceSemantics.Receipt) :
    encodeList id (receipts.map classReceiptTerm) = encodeList classReceiptTerm receipts := by
  induction receipts with
  | nil => rfl
  | cons receipt rest ih => simp only [List.map_cons, encodeList, id_eq, ih]

@[metta_head "rho:native:hit"]
theorem hit_returns (state : Effects.State) (target : Pattern) :
    ∀ receipts : List GeneralOccurrenceSemantics.Receipt,
      (∀ receipt ∈ receipts, Complete.Classes.Checked spec.plan spec.bound spec.expected receipt.target) →
      PureReturns helperLibrary.runtime [] state
        (apply "rho:native:hit" [standardAtom spec, patternValue target,
          encoded (encodeList classReceiptTerm receipts)]) state
        (Effects.boolean (receipts.any (fun receipt => committed receipt.target == target)))
  | [], _ => hit_nil_returns state _ target
  | receipt :: rest, checked => by
    have here := target_in_helper_returns state receipt (checked receipt (by simp))
    have later := hit_returns state target rest (fun other member => checked other (by simp [member]))
    by_cases same : committed receipt.target = target
    · have positive := hit_cons_hit_returns state _ (classReceiptTerm receipt)
        (rest.map classReceiptTerm) target (committed receipt.target) here same
      have wire : encodeList id (classReceiptTerm receipt :: rest.map classReceiptTerm) =
          encodeList classReceiptTerm (receipt :: rest) := encode_receipts (receipt :: rest)
      rw [wire] at positive
      simpa only [standardAtom, List.any_cons, same, BEq.rfl, Bool.true_or] using positive
    · have negative := hit_cons_miss_returns state _ (classReceiptTerm receipt)
        (rest.map classReceiptTerm) target (committed receipt.target) _ here same
        (by simpa only [standardAtom, encode_receipts] using later)
      have wire : encodeList id (classReceiptTerm receipt :: rest.map classReceiptTerm) =
          encodeList classReceiptTerm (receipt :: rest) := encode_receipts (receipt :: rest)
      rw [wire] at negative
      simpa only [standardAtom, List.any_cons, beq_eq_false_iff_ne.mpr same, Bool.false_or] using negative

set_option maxHeartbeats 4000000 in
@[metta_head "rho:native:verdict"]
theorem verdict_returns (state : Effects.State) (target : Pattern)
    (snapshot : Complete.Classes.State spec.plan)
    (checked : ∀ receipt ∈ snapshot.log,
      Complete.Classes.Checked spec.plan spec.bound spec.expected receipt.target) :
    PureReturns helperLibrary.runtime [] state
      (apply "rho:native:verdict" [standardAtom spec, patternValue target,
        classReadoutValue spec.plan snapshot]) state (verdict target snapshot).atom := by
  have tested := hit_returns state target snapshot.log checked
  by_cases hit : snapshot.log.any (fun receipt => committed receipt.target == target) = true
  · rho_native_eval [tested] unfolding [classReadoutValue, verdict, hit, Verdict.atom]
  · cases done : Complete.Classes.complete spec.plan snapshot <;>
      rho_native_eval [tested] unfolding [classReadoutValue, verdict, hit, done, Verdict.atom]

theorem fixture_verdict_returns (state : Effects.State) (fixture : Fixture) :
    PureReturns helperLibrary.runtime [] state
      (apply "rho:native:verdict" [standardAtom spec, patternValue fixture.target,
        classReadoutValue spec.plan fixture.state]) state (verdict fixture.target fixture.state).atom :=
  verdict_returns state fixture.target fixture.state
    (Complete.Classes.logChecked_rounds fixture.work
      (Complete.Classes.logChecked_begin (plan := spec.plan) (bound := spec.bound)
        (expected := spec.expected) (committed fixture.source)))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
