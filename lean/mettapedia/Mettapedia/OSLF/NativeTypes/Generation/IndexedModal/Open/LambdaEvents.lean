import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Consumers
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingObservations
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecutionControls

/-! # A generated contextual lambda site with an original beta event -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.LambdaEvents

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal
open Mettapedia.OSLF.NativeTypes.Generation
open NativeReceiptRechecking

open BindingPipeline.Installed.CertifiedExecution.Controls

def payload : Payload :=
  ⟨0, [], betaCapture, betaCapture, [], identity⟩

/-- The source event is proved independently of installation and receipt rechecking. -/
theorem original_beta_firing : Valid StructuralDescent.Controls.lambdaEnvironment []
    (.base "Term") betaSource.term payload := beta_firing

/-- Actual generation and receipt acceptance accompany the selected contextual
site. The shape checks inspect generated interfaces; they do not author them. -/
structure Event where
  installed : Joined.Installed
  generated : Consumers.generate BindingPipeline.Controls.originalLambda = .ok installed
  index : installed.Index
  position : (installed.indexed.schema index).position = [0]
  ordinal : (installed.indexed.schema index).ordinal = 0
  no_indices : (CurriedInterfaces.interface installed.indexed index).indices = []
  one_rely : (CurriedInterfaces.interface installed.indexed index).relies.length = 1
  program_sort : installed.programSort index = "Term"
  receipt : installed.Receipt index [] betaSource.term
  checked : installed.checkReceipt index [] betaSource.term payload = some receipt

namespace Event

variable (event : Event)

abbrev frame : SemanticReceipts.Frame event.installed.indexed event.installed.semantic event.index [] :=
  event.receipt.frame

theorem frame_payload : read event.frame.point.val.receipt = payload :=
  event.installed.checkReceipt_read event.checked

theorem valid : Valid event.installed.indexed.operational.Environment []
    (.base (event.installed.programSort event.index)) betaSource.term payload :=
  (event.installed.checkReceipt_sound event.checked).1

theorem selected : payload.index = (event.installed.indexed.schema event.index).ordinal :=
  (event.installed.checkReceipt_sound event.checked).2

end Event

/-- The executable fixture uses the public generator and the original receipt
checker, returning all evidence in a dependent package. -/
def generate : Except String Event := do
  match generated : Consumers.generate BindingPipeline.Controls.originalLambda with
  | .error _ => .error "Lambda generation failed"
  | .ok installed =>
      let sites := List.finRange installed.indexed.headers.length
      match found : sites.find? (fun index =>
          (installed.indexed.schema index).position == [0] &&
            (installed.indexed.schema index).ordinal == 0) with
      | none => .error "No generated function-position beta site"
      | some index =>
          have selected := List.find?_some found
          have shape : (installed.indexed.schema index).position = [0] ∧
              (installed.indexed.schema index).ordinal = 0 := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using selected
          if no_indices : (CurriedInterfaces.interface installed.indexed index).indices = [] then
            if one_rely : (CurriedInterfaces.interface installed.indexed index).relies.length = 1 then
              if program_sort : installed.programSort index = "Term" then
                match checked : installed.checkReceipt index [] betaSource.term payload with
                | none => .error "Original beta receipt rejected"
                | some receipt => .ok ⟨installed, generated, index, shape.1, shape.2,
                    no_indices, one_rely, program_sort, receipt, checked⟩
              else .error "Generated program sort differs"
            else .error "Generated contextual site does not have one rely input"
          else .error "Generated contextual site has unexpected shared indices"

/-- This checks actual generation and rechecking, including a non-root site.
The returned witness retains its source receipt and all shape proofs. -/
def control : IO Unit := do
  match generate with
  | .error issue => throw (IO.userError issue)
  | .ok event =>
      if read event.frame.point.val.receipt != payload then
        throw (IO.userError "Receipt payload changed")
      IO.println "Generated lambda function-position site and original beta event checked"

#eval control

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.LambdaEvents
