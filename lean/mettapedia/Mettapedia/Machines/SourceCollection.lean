import Mettapedia.Machines.ExecutionControl
import Mettapedia.Machines.OwnedBind
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Source collection entry and owned completion

The common operand reader selects the producer without interpreting its
physical wrapper. Its entry agrees with the maintained source machine's
collapse rule. Source finalization constructs one value from the completed
answer frontier; it does not execute an answer whose shape resembles code.

The owned completion driver uses the same buffering algorithm for ordinary
frontier publication and collection. Collection changes only the final result
shaping policy. All producer effects precede that publication; a later fault
keeps effects but discards the unpublished buffer.

These are source entry/finalization and finite completed-producer laws, not a
full compiler from source configurations to contextual CBPV. Native bodies,
conditional packets, source-fuel assignment and pointer ownership retain their
separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceCollection

open Mettapedia.Languages.MeTTa.PeTTa
open OwnedPullDriver

abbrev Atom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
abbrev Bindings := Mettapedia.Languages.ProcessCalculi.MORK.Subst

def enter (bindings : Bindings) (plan : ExecutionControl.Plan) (operands : Array Atom)
    (before : Eval.Configuration) : Option Eval.Configuration :=
  match ExecutionControl.read plan operands with
  | some (.collect body) => some {before with
      control := .evaluate bindings body, frames := .collect :: before.frames}
  | _ => none

theorem source_entry (program : SpaceSemantics.Program) (bindings : Bindings)
    (body : Atom) (before : Eval.Configuration) :
    (ExecutionControl.elaborate .collect 1).bind
        (fun plan => enter bindings plan #[body] before) =
      Eval.step program {before with
        control := .evaluate bindings (.expression [.symbol "collapse", body])} := by
  rfl

theorem source_entry_derivation (program : SpaceSemantics.Program) (bindings : Bindings)
    (body : Atom) (before : Eval.Configuration) :
    DeclarativeSpec.Transition program
      {before with control := .evaluate bindings (.expression [.symbol "collapse", body])}
      {before with control := .evaluate bindings body, frames := .collect :: before.frames} := by
  exact .collapse_enter rfl

def finish (answers : List Atom) : List Atom := [.expression answers]

/-- The independent source transition retains the store and I/O history. -/
theorem source_finalization (program : SpaceSemantics.Program) (answers : List Atom)
    (before : Eval.Configuration) :
    Eval.step program {before with
        control := .returned answers, frames := .collect :: before.frames} =
      some {before with control := .returned (finish answers)} := by
  rfl

theorem source_finalization_derivation (program : SpaceSemantics.Program)
    (answers : List Atom) (before : Eval.Configuration) :
    DeclarativeSpec.Transition program
      {before with control := .returned answers, frames := .collect :: before.frames}
      {before with control := .returned (finish answers)} := by
  exact .collapse_return rfl rfl

theorem relocated_producer (bindings : Bindings) (ignored body : Atom)
    (before : Eval.Configuration) :
    enter bindings ⟨.collect, some 1, none, none⟩ #[ignored, body] before =
      some {before with
        control := .evaluate bindings body, frames := .collect :: before.frames} := by
  rfl

theorem missing_producer_refuses (bindings : Bindings) (operands : Array Atom)
    (before : Eval.Configuration) :
    enter bindings ⟨.collect, none, none, none⟩ operands before = none := by
  rfl

def lower {Effect Reason : Type}
    (components : List (OwnedBind.NativeCompletion.Component Effect Atom Reason)) :=
  OwnedBind.NativeCompletion.lowerWith finish [] components

/-- The common completion loop publishes one aggregate only on success. -/
theorem driver_refines {Effect Reason : Type}
    (components : List (OwnedBind.NativeCompletion.Component Effect Atom Reason)) :
    ∃ allowance, advance allowance ⟨lower components, []⟩ =
      ((OwnedBind.NativeCompletion.reference components).1 ++
        (match (OwnedBind.NativeCompletion.reference components).2 with
         | .ok rows => [OwnedBind.NativeCompletion.Event.publish (.expression rows)]
         | .error _ => []),
        ⟨.done ((OwnedBind.NativeCompletion.reference components).2.map (fun _ => ())), []⟩) := by
  obtain ⟨allowance, exactRun⟩ := OwnedBind.NativeCompletion.driverWith_refines finish components
  refine ⟨allowance, ?_⟩
  cases outcome : (OwnedBind.NativeCompletion.reference components).2 <;>
    simpa [lower, finish, outcome] using exactRun

theorem effects_before_single_aggregate :
    ∃ allowance, advance allowance
      ⟨lower ([⟨[1], .ok [.symbol "same"]⟩, ⟨[2], .ok [.symbol "same"]⟩] :
        List (OwnedBind.NativeCompletion.Component Nat Atom String)), []⟩ =
      ([.effect 1, .effect 2, .publish (.expression [.symbol "same", .symbol "same"])],
        ⟨.done (.ok ()), []⟩) := by
  exact driver_refines _

theorem fault_discards_unpublished_aggregate :
    ∃ allowance, advance allowance
      ⟨lower ([⟨[1], .ok [.symbol "same"]⟩, ⟨[2], .error "fault"⟩] :
        List (OwnedBind.NativeCompletion.Component Nat Atom String)), []⟩ =
      ([.effect 1, .effect 2], ⟨.done (.error "fault"), []⟩) := by
  exact driver_refines _

theorem empty_producer_yields_one_empty_value :
    ∃ allowance, advance allowance
      ⟨lower ([] : List (OwnedBind.NativeCompletion.Component Nat Atom String)), []⟩ =
      ([.publish (.expression [])], ⟨.done (.ok ()), []⟩) := by
  exact driver_refines _

theorem completed_code_shape_stays_data (program : SpaceSemantics.Program)
    (before : Eval.Configuration) :
    let code : Atom := .expression [.symbol "empty"]
    Eval.step program {before with
      control := .returned [code, code], frames := .collect :: before.frames} =
      some {before with control := .returned [.expression [code, code]]} := by
  rfl

end Mettapedia.Machines.SourceCollection

#print axioms Mettapedia.Machines.SourceCollection.source_entry
#print axioms Mettapedia.Machines.SourceCollection.source_entry_derivation
#print axioms Mettapedia.Machines.SourceCollection.source_finalization
#print axioms Mettapedia.Machines.SourceCollection.source_finalization_derivation
#print axioms Mettapedia.Machines.SourceCollection.relocated_producer
#print axioms Mettapedia.Machines.SourceCollection.missing_producer_refuses
#print axioms Mettapedia.Machines.SourceCollection.driver_refines
#print axioms Mettapedia.Machines.SourceCollection.effects_before_single_aggregate
#print axioms Mettapedia.Machines.SourceCollection.fault_discards_unpublished_aggregate
#print axioms Mettapedia.Machines.SourceCollection.empty_producer_yields_one_empty_value
#print axioms Mettapedia.Machines.SourceCollection.completed_code_shape_stays_data
