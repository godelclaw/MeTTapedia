import Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts

open Mettapedia.OSLF.Framework

/-!
# The actual stopping horizon and its native evidence

The bounded search records the first conclusive round. This horizon is a
local exploration bound, not an aggregate instruction count. Evidence is
read from that round's actual frontier, so requesting a larger budget does
not silently display observations made after the decision stopped.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.GSLT

universe u v w

structure Record (statement : Prop) where
  horizon : Nat
  outcome : Outcome statement

def scan {statement : Prop} (evaluate : Nat → Outcome statement) (start : Nat) :
    Nat → Record statement
  | 0 => ⟨start - 1, .unknown⟩
  | remaining + 1 => match evaluate start with
    | .proved proof => ⟨start, .proved proof⟩
    | .refuted refutation => ⟨start, .refuted refutation⟩
    | .unknown => scan evaluate (start + 1) remaining

theorem scan_outcome {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget : Nat) :
    (scan evaluate start budget).outcome = Outcome.streamFrom evaluate start budget := by
  induction budget generalizing start with
  | zero => rfl
  | succ budget ih =>
    simp only [scan, Outcome.streamFrom]
    cases evaluate start <;> simp only [ih]

theorem scan_horizon_le {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget : Nat) : (scan evaluate start budget).horizon ≤ start + budget - 1 := by
  induction budget generalizing start with
  | zero => simp [scan]
  | succ budget ih =>
    simp only [scan]
    cases evaluate start with
    | proved proof => simp only; omega
    | refuted refutation => simp only; omega
    | unknown =>
      simp only
      have bound := ih (start + 1)
      omega

theorem scan_decided_at {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget : Nat) (answer : Bool)
    (decided : (scan evaluate start budget).outcome.answer = some answer) :
    (evaluate (scan evaluate start budget).horizon).answer = some answer := by
  induction budget generalizing start with
  | zero => cases decided
  | succ budget ih =>
    cases found : evaluate start with
    | proved proof => simpa only [scan, found] using decided
    | refuted refutation => simpa only [scan, found] using decided
    | unknown =>
      simpa only [scan, found] using ih (start + 1) (by simpa only [scan, found] using decided)

theorem scan_prior_unknown {statement : Prop} (evaluate : Nat → Outcome statement)
    (start budget previous : Nat)
    (afterStart : start ≤ previous) (beforeStop : previous < (scan evaluate start budget).horizon) :
    (evaluate previous).answer = none := by
  induction budget generalizing start with
  | zero => simp only [scan] at beforeStop; omega
  | succ budget ih =>
    cases found : evaluate start with
    | proved proof => simp only [scan, found] at beforeStop; omega
    | refuted refutation => simp only [scan, found] at beforeStop; omega
    | unknown =>
      by_cases same : previous = start
      · subst previous; rw [found]; rfl
      · apply ih (start + 1) (by omega)
        simpa only [scan, found] using beforeStop

def run {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    Record (denotation tests formula source) :=
  scan (fun horizon => raw backend tests horizon formula source) 1 budget

theorem run_outcome {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    (run backend tests formula source budget).outcome =
      Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend tests formula source budget :=
  (scan_outcome _ 1 budget).trans (stream_eq_check backend tests formula source budget)

theorem run_horizon_le {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    (run backend tests formula source budget).horizon ≤ budget := by
  simpa only [run, Nat.add_sub_cancel_left] using
    scan_horizon_le (fun horizon => raw backend tests horizon formula source) 1 budget

theorem run_stopped_at_answer {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) (answer : Bool)
    (decided : (run backend tests formula source budget).outcome.answer = some answer) :
    (raw backend tests (run backend tests formula source budget).horizon formula source).answer = some answer :=
  scan_decided_at _ 1 budget answer decided

/-- A frontier view retains actual typed receipt values and its checked
closure status. The view is separate from running the query: callers may
request it when they need the receipt family. -/
structure FrontierView {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (source : system.Term) where
  horizon : Nat
  receipts : List (backend.Receipt source)
  receipts_exact : receipts = backend.frontier horizon source
  closed : Bool
  closed_exact : closed = backend.closed horizon source

def frontierView {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) {tests : Leaf → Test system admitted}
    {formula : Formula Leaf} {source : system.Term}
    (record : Record (denotation tests formula source)) : FrontierView backend source where
  horizon := record.horizon
  receipts := backend.frontier record.horizon source
  receipts_exact := rfl
  closed := backend.closed record.horizon source
  closed_exact := rfl

theorem view_receipts_sound {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : Backend.{u,v} system admitted} {source : system.Term}
    (view : FrontierView backend source) (receipt : backend.Receipt source)
    (listed : receipt ∈ view.receipts) : system.Step source (backend.target source receipt) := by
  rw [view.receipts_exact] at listed
  exact backend.sound view.horizon source receipt listed

theorem view_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {backend : Backend.{u,v} system admitted} {source : system.Term}
    (view : FrontierView backend source) (complete : view.closed = true)
    (target : system.Term) (step : system.Step source target) :
    ∃ receipt, receipt ∈ view.receipts ∧ system.Equiv target (backend.target source receipt) := by
  rw [view.closed_exact] at complete
  rw [view.receipts_exact]
  exact backend.coverage view.horizon source complete target step

end Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded
