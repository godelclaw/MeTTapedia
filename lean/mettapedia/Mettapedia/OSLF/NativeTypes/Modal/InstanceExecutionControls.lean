import Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution
import Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison
import Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend

open Mettapedia.OSLF.Framework

/-!
# Original machine controls for a non-root generated modal instance

The selected generated site is the first argument of the authored Normal
constructor. Its two rely values are the actual continuation and data-list
values. The positive question names the generated ZeroCode rule's specified
Ret contractum; the negative question changes its substituted continuation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
open Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls

namespace Public

def admission : Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.SourceAdmission Source :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.localSourceAdmission (schema := schema)

def cursor : Mettapedia.OSLF.NativeTypes.Decision.Machine.CursorBackend (GeneratedInstance.system schema) Source :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.CursorBackend.cursorBackend Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated.plan
    schema.bound schema.programCarrier rfl
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_foundation)
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equations
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_generic)

def request? (permit : Bool) :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.admit? admission
    (codes permit) (decisions permit) supplied focus

def admitted (permit : Bool) : Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.AdmittedRequest
    (codes permit) supplied focus Source :=
  ⟨request permit, typed_plugged_source permit⟩

def run (permit : Bool) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.run cursor equations (decisions permit) (admitted permit) budget

def check (permit : Bool) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.checkLocal schema
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_foundation)
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equations
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_generic)
    (codes permit) (decisions permit) supplied focus budget

def budget (permit : Bool) : Nat :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.totalBound cursor equations (decisions permit) (admitted permit)

def origins (permit : Bool) (work : Nat) : List Nat :=
  (run permit work).observations.map fun observed => observed.receipt.val.firing.job.declaration.declarationIndex

end Public

theorem non_root_and_nonempty_rely : schema.position = [0] ∧ schema.relyNames = ["k", "v"] :=
  ⟨computed_schema.1, computed_schema.2.1⟩

/-- The independent original rule semantics supplies the named ZeroCode
contractum. The generated-system comparison is earned for the complete
original machine presentation, rather than defined by this control. -/
theorem original_instance_positive :
    Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus supplied (codes true).continuation) := by
  apply (GeneratedInstance.outcome_exact (request true)).mp
  refine ⟨?_, ?_⟩
  · change (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated.plan
      [] (.base "Cfg")).Step Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
        Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget
    rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
    apply (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison.generated_step_iff_original []
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source_admitted).mpr
    apply Mettapedia.Languages.PartrecMachine.reduces_iff_mem_rootReducts.mpr
    decide +kernel
  · change _ = true ∧ _ = some _ ∧ _ = some _ ∧ true = true
    exact ⟨by decide +kernel, rfl, rfl, rfl⟩

theorem false_substituted_continuation :
    ¬ Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus supplied (codes false).continuation) := by
  intro inhabited
  have continuation := (GeneratedInstance.outcome_exact (request false)).mpr inhabited
  exact Bool.noConfusion continuation.2.2.2.2

theorem generated_filling_and_contractum (permit : Bool) :
    (Public.admitted permit).request.source = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source ∧
      (Public.admitted permit).request.target = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget := ⟨rfl, rfl⟩

theorem public_complete (permit : Bool) :
    (Public.run permit (Public.budget permit)).result.Decided :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.run_complete (Public.admitted permit) _ (Nat.le_refl _)

theorem public_positive_at_bound :
    (Public.run true (Public.budget true)).answer = some true := by
  obtain ⟨answer, read⟩ := public_complete true
  cases answer with
  | true => exact read
  | false =>
    exact (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.negative (Public.run true (Public.budget true)) read
      original_instance_positive).elim

theorem public_negative_at_bound :
    (Public.run false (Public.budget false)).answer = some false := by
  obtain ⟨answer, read⟩ := public_complete false
  cases answer with
  | false => exact read
  | true =>
    exact (false_substituted_continuation
      (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.positive (Public.run false (Public.budget false)) read)).elim

theorem all_budget_splits (permit : Bool) (first more : Nat) :
    Public.run permit (first + more) =
      Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.resume more (Public.run permit first) :=
  Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.run_exact_resume (Public.admitted permit) first more

#guard (Public.request? true).isOk
#guard (Public.request? false).isOk
#guard schema.position == [0]
#guard schema.relyNames == ["k", "v"]
#guard (Public.run true 0).answer == none
#guard (Public.run true 1).answer == none
#guard (Public.run true 1000).answer == some true
#guard (Public.run false 1000).answer == some false
#guard (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.resume 999 (Public.run true 1)).answer == some true
#guard (Public.check true 1000).map (fun session => session.answer) == .ok (some true)
#guard (Public.check false 1000).map (fun session => session.answer) == .ok (some false)
#guard Public.origins true 1000 == [0]
#guard (Public.run true 1000).spent <= 1000
#guard (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.admit? Public.admission
    (codes true) (decisions true) supplied Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.nil).toOption.isNone
#guard (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecution.admit? Public.admission
    (codes true) (decisions true) [] focus).toOption.isNone

#print axioms original_instance_positive
#print axioms false_substituted_continuation

end Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls
