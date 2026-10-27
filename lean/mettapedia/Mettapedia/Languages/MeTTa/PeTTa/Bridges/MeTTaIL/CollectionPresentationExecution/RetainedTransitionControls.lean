import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperationControls

/-! Joined one-step controls include the existing pending work and the full
ordered candidate prefix, including equal target values with distinct frames. -/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionControls

open Mettapedia.GSLT.LanguageDef CettaWire
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Retained RetainedWire RetainedOperationControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit

inductive Job where
  | returned {kind : Kind} (value : Value kind) (next : Continuation kind)
  | children (query : Query .children) (next : Continuation .children)

def Job.task : Job → Task
  | .returned value next => .returned value next
  | .children query next => .request query next

def Job.expansionCode : Job → Atom
  | .returned value next => apply "gslt:collection-presentation:view-return"
      [encoded (valueTerm value),encoded (continuationTerm next)]
  | .children query next => apply "gslt:collection-presentation:view-children"
      [encoded (queryTerm query),encoded (continuationTerm next)]

def account : List Spelling := [value,otherValue,value]

def Job.code (job : Job) : Atom := RetainedTransitionJoin.commitCall pending account job.expansionCode

def Job.after (job : Job) : State := tick parameters ⟨job.task :: pending,account⟩

def jobs : List (String × Job) := controls.flatMap fun (name,operation) =>
  match operation with
  | .returned value next => [(name,Job.returned value next)]
  | .children query next => [(name,Job.children query next)]
  | _ => []

theorem native_job_returns (host : Effects.State) (job : Job) :
    PureReturns RetainedTransitionJoin.runtime [] host job.code host (encoded (stateTerm job.after)) := by
  cases job with
  | returned value next =>
      exact RetainedTransitionJoin.returned_step_returns host parameters value next pending account
  | children query next =>
      exact RetainedTransitionJoin.children_step_returns host parameters query next pending account

theorem old_account_remains_prefix (job : Job) :
    ∃ suffix, job.after.answers = account ++ suffix := by
  exact ⟨(expand parameters job.task).2,rfl⟩

theorem old_pending_remains_suffix (job : Job) :
    ∃ before, job.after.agenda = before ++ pending := by
  exact ⟨(expand parameters job.task).1,rfl⟩

#print axioms native_job_returns
#print axioms old_account_remains_prefix
#print axioms old_pending_remains_suffix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedTransitionControls
