import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureBeginExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureTickExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureReadout

/-! Budgeted execution and resumption use the same native ticks as the
retained closure machine. No host saturation algorithm is involved. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem advance_returns (state : State) (prepared : Executable.Prepared) (before : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (machine : ClosureMachine.Machine prepared) (ready : ClosureMachine.Ready prepared machine) (ticks quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:advance" [encoded (ClosureMachine.machineTerm prepared machine),number ticks,number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared (ClosureMachine.advance prepared ticks quantum machine))) := by
  induction ticks generalizing machine with
  | zero =>
    metta_call checked
    metta_eval with checked unfolding [ClosureMachine.advance]
  | succ ticks ih =>
    have stepped := tick_returns state prepared before admitted machine ready quantum
    have continued := ih (ClosureMachine.tick prepared machine quantum)
      (ClosureMachine.tick_ready prepared before admitted machine ready quantum)
    metta_call checked
    metta_eval [stepped,continued] with checked unfolding [ClosureMachine.advance]

theorem run_returns (state : State) (prepared : Executable.Prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true) (ticks quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:advance"
        [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared
        (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) :=
  advance_returns state prepared _ admitted _ (ClosureMachine.begin_ready prepared admitted) ticks quantum

theorem resume_returns (state : State) (prepared : Executable.Prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true) (first second quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:advance"
        [encoded (ClosureMachine.machineTerm prepared
          (ClosureMachine.advance prepared first quantum (ClosureMachine.begin prepared))),number second,number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared
        (ClosureMachine.advance prepared (first+second) quantum (ClosureMachine.begin prepared)))) := by
  rw [ClosureMachine.advance_add]
  exact advance_returns state prepared _ admitted _
    (ClosureMachine.advance_ready prepared _ admitted _ (ClosureMachine.begin_ready prepared admitted) first quantum) second quantum

theorem advance_completed_iff (state after : State) (prepared : Executable.Prepared) (before : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (machine : ClosureMachine.Machine prepared) (ready : ClosureMachine.Ready prepared machine)
    (ticks quantum : Nat) (answers input output : List OSLFCore.Atom) :
    (∃ fuel, Eval.run runtime fuel
      {state,control := .evaluate [] (apply "gslt:snapshot:advance"
        [encoded (ClosureMachine.machineTerm prepared machine),number ticks,number quantum])} =
      .complete after answers input output) ↔
    after = state ∧
      answers = [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.advance prepared ticks quantum machine))] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff _ _ _ _ _ _
    (advance_returns state prepared before admitted machine ready ticks quantum) _ _ _ _

#print axioms advance_returns
#print axioms run_returns
#print axioms resume_returns
#print axioms advance_completed_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
