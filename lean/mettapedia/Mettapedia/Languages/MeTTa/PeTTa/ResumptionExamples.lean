import Mettapedia.Languages.MeTTa.PeTTa.Resumption

/-!
# Retained configuration resumption controls

The examples use the existing executable configuration machine. They retain
a captured binding, repeated alternatives and an already performed output.
Replacing a residual with an unrelated expression loses that information.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval.ResumptionExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def program : SpaceSemantics.Program := { equations := [], declarations := [] }

def seven : Atom := .grounded (.int 7)

def repeated : Atom := .expression
  [.symbol "let", .var "held", seven,
   .expression [.symbol "superpose", .expression [.var "held", .var "held"]]]

def captured : Configuration :=
  { state := Effects.empty, control := .returned [seven],
    frames := [.bind [] (.var "held")
      (.expression [.symbol "superpose", .expression [.var "held", .var "held"]])] }

theorem pause_retains_binding_frame :
    run program 2 (start Effects.empty repeated) = .exhausted captured := by
  rfl

def readout : Outcome → Option (List Atom × List Atom × List Atom)
  | .complete _ answers input output => some (answers, input, output)
  | _ => none

theorem resumed_retains_both_occurrences :
    readout (resume program 20 (.exhausted captured)) =
      some ([seven, seven], [], []) := by
  decide +kernel

theorem resumed_equals_uninterrupted :
    resume program 20 (run program 2 (start Effects.empty repeated)) =
      run program 22 (start Effects.empty repeated) :=
  resume_run program 2 20 _

theorem bare_variable_loses_capture :
    run program 20 (start Effects.empty (.var "held")) ≠
      resume program 20 (.exhausted captured) := by
  intro same
  have different := congrArg readout same
  exact (by decide +kernel :
    readout (run program 20 (start Effects.empty (.var "held"))) ≠
      readout (resume program 20 (.exhausted captured))) different

def message : Atom := .grounded (.string "once")

def printing : Configuration :=
  { state := Effects.empty,
    control := .arguments [] (.function "println!") [] [message] 1,
    frames := [.collect] }

def printed : Configuration :=
  { state := Effects.empty, control := .returned [Effects.boolean true],
    frames := [.collect], output := [message] }

theorem pause_retains_performed_output :
    run program 1 printing = .exhausted printed := by
  rfl

theorem resuming_does_not_repeat_output :
    resume program 1 (.exhausted printed) =
      .complete Effects.empty [.expression [Effects.boolean true]] [] [message] := by
  rfl

theorem changing_endpoint_is_observable :
    resume program 1 (.exhausted printed) ≠
      run program 1 { printed with output := [] } := by
  intro same
  have different := congrArg
    (fun outcome => match outcome with
      | .complete _ _ _ output => output.length
      | _ => 0) same
  exact (by decide : (1 : Nat) ≠ 0) different

end Mettapedia.Languages.MeTTa.PeTTa.Eval.ResumptionExamples
