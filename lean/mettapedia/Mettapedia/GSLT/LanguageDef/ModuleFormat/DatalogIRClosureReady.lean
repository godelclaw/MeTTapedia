import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotRows
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner

/-! Readiness for the shared class-search operations follows from the actual
compiled admission result. A replacement snapshot earns its own readiness
through checked rows; the original compiled code and free types stay fixed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Complete.Footprint

theorem admitted_scope (prepared : Executable.Prepared) (before after : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (closed : ClosureMachine.closed prepared after = true) :
    Scope (Executable.plan prepared after) (declaredFootprint (Executable.plan prepared after)) ∧
      (Executable.plan prepared after).snapshot.free.entriesOn
        (declaredFootprint (Executable.plan prepared after)) = Executable.freeTypes prepared.vocabulary := by
  have complete := Executable.snapshot_admission_transport prepared before after admitted closed
  have empty : (Executable.plan prepared after).obligations = [] := List.isEmpty_iff.mp complete
  exact Complete.Footprint.compiled_scope (snapshot := Executable.snapshot prepared after)
    (permissions := Executable.permissions) (by rw [show (GeneralExecutionAdmission.compile
      (Executable.snapshot prepared after) Executable.permissions).obligations = [] from empty]; rfl) rfl

theorem request_within (prepared : Executable.Prepared) (facts : List Pattern) :
    ∀ name ∈ (Executable.request prepared.vocabulary).freeFvarNames,
      name ∈ declaredFootprint (Executable.plan prepared facts) := by
  intro name present
  apply List.mem_append_left
  change name ∈ (Executable.freeTypes prepared.vocabulary).map Prod.fst
  simpa [Executable.request,Query.call,Join.vector,Pattern.freeFvarNames,
    Executable.freeTypes,Executable.relationRef,Executable.valueRef,
    List.flatMap_map,List.map_map,Function.comp_def,eq_comm] using present

theorem initial_search_ready (prepared : Executable.Prepared) (before facts : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (closed : ClosureMachine.closed prepared facts = true) :
    CompleteExecution.SearchReady [] (.base "DlStatement")
      (declaredFootprint (Executable.plan prepared facts))
      ((search prepared facts).run (Executable.request prepared.vocabulary) 0) := by
  have scope := (admitted_scope prepared before facts admitted closed).1
  exact CompleteExecution.searchReady_begin scope (request_within prepared facts)

#print axioms admitted_scope
#print axioms request_within
#print axioms initial_search_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
