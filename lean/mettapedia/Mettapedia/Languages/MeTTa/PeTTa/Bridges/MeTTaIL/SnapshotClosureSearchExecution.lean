import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosurePlanExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureReady

/-! The snapshot loop uses the existing class-search boundary. Readiness is
derived from checked compilation and replacement rows; no separate search
implementation is introduced. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open Complete.Footprint

theorem search_zero_returns (state : State) (prepared : Executable.Prepared) (before facts : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (closed : ClosureMachine.closed prepared facts = true) :
    PureReturns runtime [] state
      (apply "gslt:search:run" [CompleteExecution.classSearchBackend,
        encoded (CompletePlanWire.planTerm (Executable.plan prepared facts)
          (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
        encoded (InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary)),number 0]) state
      (encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts)
        ((ClosureMachine.search prepared facts).run (Executable.request prepared.vocabulary) 0))) := by
  have scope := ClosureMachine.admitted_scope prepared before facts admitted closed
  have run := CompleteExecution.search_run_zero_returns (Executable.plan prepared facts) state
    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")
    (declaredFootprint (Executable.plan prepared facts)) scope.2.symm scope.1.declared
    (Executable.request prepared.vocabulary) (ClosureMachine.request_within prepared facts)
  metta_lift checked ["backend","plan","source","work"] run

theorem search_resume_returns (state : State) (prepared : Executable.Prepared) (before facts : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (closed : ClosureMachine.closed prepared facts = true)
    (run : Complete.Classes.State (Executable.plan prepared facts))
    (ready : CompleteExecution.SearchReady [] (.base "DlStatement")
      (declaredFootprint (Executable.plan prepared facts)) run) (quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:search:resume" [CompleteExecution.classSearchBackend,
        encoded (CompletePlanWire.planTerm (Executable.plan prepared facts)
          (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
        encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts) run),number quantum]) state
      (encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts)
        ((ClosureMachine.search prepared facts).resume run quantum))) := by
  have scope := ClosureMachine.admitted_scope prepared before facts admitted closed
  have resumed := CompleteExecution.search_resume_returns (Executable.plan prepared facts) state
    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")
    (declaredFootprint (Executable.plan prepared facts)) scope.2.symm scope.1 run ready quantum
  metta_lift checked ["backend","plan","run","work"] resumed

theorem search_publication_returns (state : State) (prepared : Executable.Prepared) (facts : List Pattern)
    (run : Complete.Classes.State (Executable.plan prepared facts)) :
    PureReturns runtime [] state
      (apply "gslt:search:publication" [CompleteExecution.classSearchBackend,
        encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts) run)]) state
      (encoded (encodeList CompleteExecution.classReceiptTerm ((ClosureMachine.search prepared facts).publication run))) := by
  metta_lift checked ["backend","run"]
    (CompleteExecution.search_publication_returns (Executable.plan prepared facts) state run)

theorem search_status_returns (state : State) (prepared : Executable.Prepared) (facts : List Pattern)
    (run : Complete.Classes.State (Executable.plan prepared facts))
    (ready : CompleteExecution.SearchReady [] (.base "DlStatement")
      (declaredFootprint (Executable.plan prepared facts)) run) :
    PureReturns runtime [] state
      (apply "gslt:search:status" [CompleteExecution.classSearchBackend,
        encoded (CompletePlanWire.planTerm (Executable.plan prepared facts)
          (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
        encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts) run)]) state
      (CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared facts).status run)) := by
  have status := CompleteExecution.search_status_returns (Executable.plan prepared facts) state
    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement") run
    (fun entry member => CompleteExecution.key_licensed_of_ready (ready.1.entries entry member))
  metta_lift checked ["backend","plan","run"] status

#print axioms search_zero_returns
#print axioms search_resume_returns
#print axioms search_publication_returns
#print axioms search_status_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
