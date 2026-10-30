import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

/-! The public result operation reads the retained machine's observation.
Faults remain faults, and a pending machine is never read as completed. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem result_returns (state : State) (prepared : Executable.Prepared)
    (machine : ClosureMachine.Machine prepared) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:result" [encoded (ClosureMachine.machineTerm prepared machine)])
      state (encoded (ClosureMachine.resultTerm prepared machine)) := by
  cases fault : machine.fault with
  | none =>
    metta_call checked
    metta_eval with checked unfolding [ClosureMachine.machineTerm,ClosureMachine.resultTerm,fault]
  | some failure =>
    cases failure <;>
      metta_call checked <;>
      metta_eval with checked unfolding [ClosureMachine.machineTerm,ClosureMachine.resultTerm,fault]

#print axioms result_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
