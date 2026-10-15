import Mettapedia.OSLF.MeTTaIL.GeneralRhoOrigins
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination

/-!
# Executed reflective rho controls

The selected COMM source executes received drops, preserves an outer bound
name, and retains duplicate input origins. A source with a process in a Name
position is rejected by the real grammar gate. The receipt beneath an input
binder carries the complete typed zipper and actual source body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho.Controls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open GeneralPremise.Execution GeneralScopedMatchMachine

def zero : Pattern := .apply "PZero" []
def channel : Pattern := .apply "NQuote" [zero]
def receivedBody : Pattern := .apply "PDrop" [.bvar 0]
def outerBody : Pattern := .apply "PDrop" [.bvar 1]

def runtimeEnvironment : GeneralPremise.Environment where
  language := {language with rewrites := [comm]}
  free := snapshot.free
  provider := snapshot.provider
  specifications := [(0, Mettapedia.GSLT.Examples.ScopedRhoBinding.scopedCommBindingSpec)]
  reflection := Mettapedia.GSLT.LanguageDef.ReflectionExtension.rhoReflectionProfile

theorem runtime_environment_actual : executionEnvironment = runtimeEnvironment := by
  unfold executionEnvironment GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

def goal (bound : List TypeExpr) (name body : Pattern) : Goal :=
  .root bound (.base "Proc") (source name body zero []) 0

def finished (bound : List TypeExpr) (name body : Pattern) :=
  GeneralPremise.Execution.run runtimeEnvironment (goal bound name body) 80
    (GeneralPremise.Execution.start runtimeEnvironment (goal bound name body))

def targets (bound : List TypeExpr) (name body : Pattern) :
    Result runtimeEnvironment (goal bound name body) → Pattern
  | .root _ _ _ _ target _ => target

theorem actual_received_drop :
    (finished [] channel receivedBody).answers.map (targets [] channel receivedBody) =
      [.collection .hashBag [zero] none] := by decide +kernel

theorem actual_outer_name_retained :
    (finished [.base "Name"] (.bvar 0) outerBody).answers.map
      (targets [.base "Name"] (.bvar 0) outerBody) =
      [.collection .hashBag [.apply "PDrop" [.bvar 0]] none] := by decide +kernel

theorem actual_root_completed :
    GeneralPremise.Execution.complete runtimeEnvironment (goal [] channel receivedBody)
      (finished [] channel receivedBody) = true := by decide +kernel

theorem pause_inside_actual_matching :
    let query := request 0 channel receivedBody zero []
    (GeneralScopedMatchMachine.run query 5 (GeneralScopedMatchMachine.start query)).answers = [] ∧
      GeneralScopedMatchMachine.complete
        (GeneralScopedMatchMachine.run query 5 (GeneralScopedMatchMachine.start query)) = false := by
  decide +kernel

def duplicateRequest : GeneralScopedMatchMachine.Request :=
  {request 0 channel receivedBody zero [] with target := duplicateSource channel receivedBody zero}

theorem actual_duplicate_input_answers :
    (GeneralScopedMatchMachine.run duplicateRequest 100 (GeneralScopedMatchMachine.start duplicateRequest)).answers.map
      (fun answer => (answer.assignment, answer.trace)) =
      [(captured 0 channel receivedBody zero [input channel receivedBody], firstInputTrace),
        (captured 0 channel receivedBody zero [input channel receivedBody], secondInputTrace)] := by decide +kernel

theorem actual_duplicate_input_finished :
    GeneralScopedMatchMachine.complete
      (GeneralScopedMatchMachine.run duplicateRequest 100 (GeneralScopedMatchMachine.start duplicateRequest)) = true := by
  decide +kernel

theorem ill_typed_channel_has_no_firing :
    (finished [] zero receivedBody).answers = [] := by decide +kernel

theorem concrete_input_receipt :
    (inputReceipt [] channel (.bvar 0) receivedBody zero []).Valid plan [] (.base "Proc")
      (input channel (source (.bvar 0) receivedBody zero [])) := by
  apply input_receipt_valid
  · exact checkOpenPatternWellSorted_sound (by decide +kernel)
  · exact checkOpenPatternWellSorted_sound (by decide +kernel)
  · exact checkOpenPatternWellSorted_sound (by decide +kernel)
  · rfl
  · rfl
  · exact checkOpenPatternWellSorted_sound (by decide +kernel)
  · exact .nil _ _
  · intro pattern member
    simp at member

theorem concrete_input_binders_and_address :
    (inputReceipt [] channel (.bvar 0) receivedBody zero []).job.site.address = [1, 0] ∧
      (inputReceipt [] channel (.bvar 0) receivedBody zero []).job.site.focusBound = [.base "Name"] ∧
      (inputReceipt [] channel (.bvar 0) receivedBody zero []).target =
        input channel (.collection .hashBag [zero] none) := by
  refine ⟨rfl, rfl, ?_⟩
  change input channel (.collection .hashBag [reflectiveBody receivedBody zero] none) = _
  unfold receivedBody
  rw [reflective_body_received_drop]
  rfl

#print axioms actual_received_drop
#print axioms actual_outer_name_retained
#print axioms actual_duplicate_input_answers
#print axioms concrete_input_receipt

end Mettapedia.OSLF.MeTTaIL.GeneralRho.Controls
