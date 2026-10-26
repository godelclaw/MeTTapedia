import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentCodec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
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

namespace Interpreted

variable (matcher : MatchingExecution) (codec : RetainedMatchingWire.MatchingCodec matcher)

/-- The selected matcher representation is retained in the initial scheduler. -/
theorem descent_start_returns (state : State) (environment : Environment) (goal : Goal) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:start" [goalValue goal]) state
      (encoded (RetainedMatchingWire.Scheduled.stateTerm codec
        (StructuralDescent.Scheduled.start environment goal matcher))) := by
  metta_call descent_checked
  metta_eval unfolding [goalValue, RetainedMatchingWire.Scheduled.stateTerm,
    PremiseSchedulerExecution.schedulerStateTerm, StructuralDescent.Scheduled.start,
    RetainedMatchingWire.Scheduled.taskTerm, RetainedMatchingWire.Scheduled.continuationTerm, encodeList]

/-- Payload extraction keeps each selected matcher's complete answer encoding. -/
theorem descent_payloads_returns (state : State) {environment : Environment} {goal : Goal}
    (results : List (StructuralDescent.Scheduled.Interpreted.Result matcher environment goal)) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:payloads"
      [encoded (encodeList (RetainedMatchingWire.Scheduled.resultTerm codec) results)]) state
      (encoded (encodeList (RetainedMatchingWire.Scheduled.answerTerm codec) results)) := by
  induction results with
  | nil =>
    metta_call descent_checked
    metta_eval unfolding [encodeList]
  | cons result rest ih =>
    metta_call descent_checked
    metta_eval [ih] with descent_checked unfolding [encodeList, RetainedMatchingWire.Scheduled.resultTerm]

/-- Answers and unresolved depth cuts remain separate components of readout. -/
def readoutValue {environment : Environment} {goal : Goal}
    (state : StructuralDescent.Scheduled.State environment goal matcher) : Atom :=
  .expression [.symbol "DescentReadout",
    encoded (encodeList (RetainedMatchingWire.Scheduled.answerTerm codec) state.answers),
    Effects.boolean (state.unresolved.any Complete.Deep.isCut)]

theorem descent_readout_returns (state : State) {environment : Environment} {goal : Goal}
    (search : StructuralDescent.Scheduled.State environment goal matcher) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:readout"
      [encoded (RetainedMatchingWire.Scheduled.stateTerm codec search)]) state
      (readoutValue matcher codec search) := by
  metta_call descent_checked
  metta_eval [descent_payloads_returns matcher codec state search.answers,
      descent_cut_returns state search.unresolved] with descent_checked
    unfolding [RetainedMatchingWire.Scheduled.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      readoutValue, obligationsValue]

end Interpreted

/-- `gslt:descent:start` is the ordinary scheduled machine's start. -/
@[metta_head "gslt:descent:start"]
theorem descent_start_returns (state : State) (environment : Environment) (goal : Goal) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:start" [goalValue goal]) state
      (descentStateValue (StructuralDescent.Scheduled.start environment goal)) := by
  simpa only [descentStateValue, RetainedMatchingWire.Scheduled.ordinary_state] using
    Interpreted.descent_start_returns MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec
      state environment goal

/-- `gslt:descent:payloads` keeps the answers of results, without their goals. -/
@[metta_head "gslt:descent:payloads"]
theorem descent_payloads_returns (state : State) {environment : Environment} {goal : Goal}
    (results : List (Result environment goal)) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:descent:payloads" [encoded (encodeList resultTerm results)])
      state (encoded (encodeList answerTerm results)) := by
  have resultEncoding : (RetainedMatchingWire.Scheduled.resultTerm RetainedMatchingWire.ordinaryCodec :
      Result environment goal → Term) = resultTerm := funext RetainedMatchingWire.Scheduled.ordinary_result
  have answerEncoding : (RetainedMatchingWire.Scheduled.answerTerm RetainedMatchingWire.ordinaryCodec :
      Result environment goal → Term) = answerTerm := funext RetainedMatchingWire.Scheduled.ordinary_answer
  simpa only [resultEncoding, answerEncoding] using
    Interpreted.descent_payloads_returns MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec state results

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
  have answerEncoding : (RetainedMatchingWire.Scheduled.answerTerm RetainedMatchingWire.ordinaryCodec :
      Result environment goal → Term) = answerTerm := funext RetainedMatchingWire.Scheduled.ordinary_answer
  simpa only [descentStateValue, RetainedMatchingWire.Scheduled.ordinary_state,
    Interpreted.readoutValue, readoutValue, answerEncoding] using
    Interpreted.descent_readout_returns MatchingExecution.ordinary RetainedMatchingWire.ordinaryCodec state search

#print axioms Interpreted.descent_start_returns
#print axioms Interpreted.descent_payloads_returns
#print axioms Interpreted.descent_readout_returns
#print axioms descent_start_returns
#print axioms descent_payloads_returns
#print axioms descent_readout_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
