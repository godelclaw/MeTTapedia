import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Lower
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage
import Mettapedia.OSLF.MeTTaIL.Complete.Deep

/-!
# Starting and reading the descent machine
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

abbrev goalValue (goal : Goal) : Atom := encoded (goalTerm goal)
abbrev descentStateValue {environment : Environment} {goal : Goal}
    (state : StructuralDescent.Scheduled.State environment goal) : Atom := encoded (stateTerm state)
abbrev obligationsValue (obligations : List Obligation) : Atom := encoded (encodeList obligationTerm obligations)

/-- `gslt:descent:start` is the scheduled machine's start. -/
@[metta_head "gslt:descent:start"]
theorem descent_start_returns (state : State) (environment : Environment) (goal : Goal) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:start" [goalValue goal]) state
      (descentStateValue (StructuralDescent.Scheduled.start environment goal)) := by
  metta_call descent_checked
  metta_eval unfolding [descentStateValue, goalValue, stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
    StructuralDescent.Scheduled.start, taskTerm, continuationTerm, encodeList]

/-- `gslt:descent:cut` says whether a depth cut is among the obligations. -/
@[metta_head "gslt:descent:cut"]
theorem descent_cut_returns (state : State) (obligations : List Obligation) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:cut" [obligationsValue obligations]) state
      (Effects.boolean (obligations.any Complete.Deep.isCut)) := by
  induction obligations with
  | nil =>
    metta_call descent_checked
    metta_eval unfolding [obligationsValue, encodeList, Effects.boolean]
  | cons obligation rest ih =>
    metta_call descent_checked
    cases obligation <;> metta_eval [ih] with descent_checked
      unfolding [obligationsValue, obligationTerm, encodeList, Effects.boolean, Complete.Deep.isCut]

/-- `gslt:descent:payloads` keeps the answers of results, without their goals. -/
@[metta_head "gslt:descent:payloads"]
theorem descent_payloads_returns (state : State) {environment : Environment} {goal : Goal}
    (results : List (Result environment goal)) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:payloads" [encoded (encodeList resultTerm results)])
      state (encoded (encodeList answerTerm results)) := by
  induction results with
  | nil =>
    metta_call descent_checked
    metta_eval unfolding [encodeList]
  | cons result rest ih =>
    metta_call descent_checked
    metta_eval [ih] with descent_checked unfolding [encodeList, resultTerm]

/-- The readout of a drained search: its answers, and whether a branch was cut. -/
def readoutValue {environment : Environment} {goal : Goal} (state : StructuralDescent.Scheduled.State environment goal) :
    Atom :=
  .expression [.symbol "DescentReadout", encoded (encodeList answerTerm state.answers),
    Effects.boolean (state.unresolved.any Complete.Deep.isCut)]

/-- `gslt:descent:readout` is the answers and the cut flag. -/
@[metta_head "gslt:descent:readout"]
theorem descent_readout_returns (state : State) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:readout" [descentStateValue search]) state
      (readoutValue search) := by
  metta_call descent_checked
  metta_eval [descent_payloads_returns state search.answers, descent_cut_returns state search.unresolved]
    with descent_checked unfolding [descentStateValue, stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      readoutValue, obligationsValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
