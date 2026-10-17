import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-!
# The scoped library's proved operations, in the complete machine's runtime

The ordered premise machine's bridges prove the scoped library's operations over
`RuleExecutionProgram.scopedMachineProgram`, the scoped source without its two rule-job readout
heads. That fragment is closed under its heads and agrees with the whole scoped source on them, and
each library above keeps them. So every such fact holds in the descent machine's runtime and in the
complete machine's runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Effects (State)
open Eval
open BridgeKit

/-- The heads of the scoped machine fragment. -/
def machineOwns (head : String) : Bool :=
  head != "gslt:rule:site-replacement-represented" && head != "gslt:rule:job-finish-root"

set_option maxRecDepth 100000 in
theorem scopedMachine_closed : ProgramClosed machineOwns RuleExecutionProgram.scopedMachineProgram :=
  closed_of_all _ _ (by decide) (by decide +kernel)

theorem scopedMachine_agreement :
    ProgramAgreementOn machineOwns RuleExecutionProgram.scopedMachineProgram scopedLibrary.runtime :=
  fragment_agreement _ _ rfl rfl fun _ owned => owned

/-- The heads every library above the scoped source leaves alone. -/
def lowerHeads (head : String) : Bool :=
  machineOwns head && !head.startsWith "gslt:sites:" && !head.startsWith "gslt:descent:"

private theorem lower_machine {head : String} (lower : lowerHeads head = true) : machineOwns head = true := by
  simp only [lowerHeads, Bool.and_eq_true] at lower
  exact lower.1.1

private theorem lower_typed {head : String} (lower : lowerHeads head = true) : typedLibrary.inherited head = true := by
  simp only [lowerHeads, Bool.and_eq_true, Bool.not_eq_true'] at lower
  simp [BridgeKit.Library.inherited, BridgeKit.Library.owns, typedLibrary, lower.1.2]

private theorem lower_descent {head : String} (lower : lowerHeads head = true) :
    descentLibrary.inherited head = true := by
  simp only [lowerHeads, Bool.and_eq_true, Bool.not_eq_true'] at lower
  simp [BridgeKit.Library.inherited, BridgeKit.Library.owns, descentLibrary, lower.2]

/-- **A scoped-machine fact holds in the descent machine's runtime.** -/
theorem lower_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin lowerHeads code = true)
    (returned : PureReturns RuleExecutionProgram.scopedMachineProgram caller state code state answer) :
    PureReturns descentLibrary.runtime caller state code state answer := by
  have whole := transport scopedMachine_closed scopedMachine_agreement
    (codeWithin_mono (fun _ lower => lower_machine lower) code supported) returned
  have typed := typedLibrary.lift typed_checked (codeWithin_mono (fun _ lower => lower_typed lower) code supported) whole
  exact descentLibrary.lift descent_checked (codeWithin_mono (fun _ lower => lower_descent lower) code supported) typed

/-- Lower a fact about a scoped-machine head at values into the descent machine's runtime:
`metta_lower [names] fact`, one distinct name per value. -/
syntax "metta_lower " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_lower [$names,*] $fact) => `(tactic|
      metta_lift descent_checked [$names,*]
        (by metta_lift typed_checked [$names,*]
          (transport_call scopedMachine_closed scopedMachine_agreement (by decide +kernel) (by decide)
            (by decide +kernel) (by decide) [$names,*] (by decide) rfl (by decide +kernel) $fact)))

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
