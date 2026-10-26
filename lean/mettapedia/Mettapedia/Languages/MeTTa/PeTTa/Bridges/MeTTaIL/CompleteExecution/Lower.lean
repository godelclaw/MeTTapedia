import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-!
# Scoped primitive operations in the shared runtime

The scoped machine's primitive fragment is closed and retains its ordered
equations and argument demands in the interpreted program. Operations in that
fragment transfer directly to the common runtime. Query and scheduler operations
whose bodies select a matching implementation are proved at their own interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Effects (State)
open Eval BridgeKit

/-- The scoped primitives retained by the selected interpreted source. -/
def lowerHeads : String → Bool := RetainedMatchingWire.scopedPrimitiveHeads

theorem scopedMachine_closed :
    ProgramClosed lowerHeads RuleExecutionProgram.scopedMachineProgram :=
  RetainedMatchingWire.scopedPrimitive_closed

theorem scopedMachine_agreement :
    ProgramAgreementOn lowerHeads RuleExecutionProgram.scopedMachineProgram descentLibrary.runtime :=
  RetainedMatchingWire.scopedPrimitive_agreement

/-- A scoped primitive computation has the same result in the shared runtime. -/
theorem lower_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin lowerHeads code = true)
    (returned : PureReturns RuleExecutionProgram.scopedMachineProgram caller state code state answer) :
    PureReturns descentLibrary.runtime caller state code state answer :=
  transport scopedMachine_closed scopedMachine_agreement supported returned

/-- Transfer a primitive call after binding its values to distinct names. -/
syntax "metta_lower " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_lower [$names,*] $fact) => `(tactic|
      exact transport_call scopedMachine_closed scopedMachine_agreement
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
        [$names,*] (by decide) rfl (by decide +kernel) $fact)

namespace Interpreted

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open WireKit

/-- A bare premise environment selects the ordinary matching implementation. -/
theorem ordinary_environment_returns (state : State) (environment : Environment)
    (free : List (String × TypeExpr)) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:premise:matching-environment"
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)]) state
      (encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)) := by
  metta_call descent_checked
  metta_eval unfolding [PremiseOperationsExecution.GeneralExecution.environmentTerm]

end Interpreted

#print axioms scopedMachine_closed
#print axioms scopedMachine_agreement
#print axioms lower_returns
#print axioms Interpreted.ordinary_environment_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
