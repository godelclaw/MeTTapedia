import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceObservation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentExpand
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution

/-!
# Native source observations through the proved descent executor

The generated expression runs the actual scheduled descent code and returns
its complete source payloads, pending-work flag and retained machine state.
The envelope retains both the source goal and the finite operational
environment. A decoded envelope alone is not evidence of a complete search:
the execution correspondence supplies its replay provenance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal NativeReceiptRechecking
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open MeTTaIL CompleteExecution WireKit DescentCodec BridgeKit
open Eval

private theorem payloads_term (environment : Environment) (source : Source)
    (snapshot : Snapshot environment source) :
    encodeList answerTerm snapshot.answers =
      encodeList ReceiptCodec.encodePayload (observe environment source snapshot).payloads := by
  simp only [observe, Scheduled.receipts, List.map_map, encodeList_map]
  congr 1
  funext result
  exact ReceiptCodec.answerTerm_eq_encodePayload result

private abbrev v (name : String) : Atom := .var name

private theorem quoted_returns (program : SpaceSemantics.Program)
    (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (state : Effects.State)
    (code answer : Atom)
    (same : Mettapedia.Languages.ProcessCalculi.MORK.applySubst caller code = answer) :
    PureReturns program caller state (apply "quote" [code]) state answer :=
  same ▸ Eval.quote_returns program caller state code

private theorem agenda_empty_returns (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : Effects.State) {environment : Environment} {goal : Scheduled.Goal}
    (agenda : List (Scheduled.Task environment goal))
    (found : caller.lookup "native:agenda" = some (encoded (encodeList taskTerm agenda))) :
    PureReturns descentLibrary.runtime caller state
      (apply "==" [v "native:agenda", .symbol "LNil"]) state (Effects.boolean agenda.isEmpty) := by
  have compared := term_equal_returns descentLibrary.runtime caller state
    (v "native:agenda") (.symbol "LNil") (encodeList taskTerm agenda) (.symbol "LNil")
    (bound_returns _ _ _ found) (Eval.symbol_returns _ _ _ _)
  cases agenda <;> simpa only [encodeList, List.isEmpty_nil, List.isEmpty_cons,
    reduceCtorEq, decide_true, decide_false] using compared

/-- A case over the actual returned scheduler state. No logical fuel value
is interpreted as a completion flag. -/
def readoutBody (environment goal : Term) : Atom :=
  apply "case" [v "native:state", .expression [
    .expression [apply "PremiseState" [v "native:agenda", v "native:answers",
      v "native:unresolved", v "native:work"],
      apply "let" [v "native:payloads", apply "gslt:descent:payloads" [v "native:answers"],
        apply "let" [v "native:settled", apply "if" [apply "==" [v "native:agenda", .symbol "LNil"],
          .symbol "NativeSettled", .symbol "NativePending"],
          apply "quote" [apply "NativeSourceReadout" [encoded environment, encoded goal, v "native:state",
            v "native:settled", v "native:payloads"]]]]]]]

def readoutCode (environment goal : Term) (snapshot : Atom) : Atom :=
  apply "let" [v "native:state", snapshot, readoutBody environment goal]

def resumeCode (environment : Environment) (source : Source) (snapshot : Term) (fuel : Nat) : Atom :=
  readoutCode (environmentTerm environment source) (goalTerm (sourceGoal environment source))
    (apply "gslt:descent:run" [encoded (environmentTerm environment source), number fuel, encoded snapshot])

def startCode (environment : Environment) (source : Source) (fuel : Nat) : Atom :=
  resumeCode environment source
    (stateTerm (Scheduled.begin environment source.bound source.type source.term)) fuel

theorem readout_returns (state : Effects.State) (environment : Environment) (source : Source)
    (snapshot : Snapshot environment source) (code : Atom)
    (returns : PureReturns descentLibrary.runtime [] state code state (descentStateValue snapshot)) :
    PureReturns descentLibrary.runtime [] state
      (readoutCode (environmentTerm environment source) (goalTerm (sourceGoal environment source)) code)
      state (encoded (observe environment source snapshot).term) := by
  have payloads := descent_payloads_returns state snapshot.answers
  rw [payloads_term environment source snapshot] at payloads
  unfold readoutCode
  apply pure_let_returns _ _ _ _ _ _ _ _ rfl
  · exact returns
  · cases agenda : snapshot.agenda with
    | nil =>
      metta_eval [payloads] with descent_checked
        unfolding [readoutBody, v, observe, Observation.term, descentStateValue, stateTerm,
          PremiseSchedulerExecution.schedulerStateTerm, agenda]
      apply pure_let_returns _ _ _ _ _ _ _ _ rfl
      · apply pure_if_returns
        · exact agenda_empty_returns _ _ (environment := environment)
            (goal := sourceGoal environment source) [] rfl
        · exact Eval.symbol_returns _ _ _ "NativeSettled"
      · apply quoted_returns
        simp [observe, Observation.term, stateTerm, encoded,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          PremiseSchedulerExecution.schedulerStateTerm, agenda]
    | cons first rest =>
      metta_eval [payloads] with descent_checked
        unfolding [readoutBody, v, observe, Observation.term, descentStateValue, stateTerm,
          PremiseSchedulerExecution.schedulerStateTerm, agenda]
      apply pure_let_returns _ _ _ _ _ _ _ _ rfl
      · apply pure_if_returns
        · exact agenda_empty_returns _ _ (first :: rest) rfl
        · exact Eval.symbol_returns _ _ _ "NativePending"
      · apply quoted_returns
        simp [observe, Observation.term, stateTerm, encoded,
          CettaWireAtom.encode, CettaWireAtom.encodeMany,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
          Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
          Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          PremiseSchedulerExecution.schedulerStateTerm, agenda]

private theorem provider_within (environment : Environment) (source : Source) :
    ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint environment source := by
  intro name member
  exact List.mem_append_left _ member

private theorem goal_within (environment : Environment) (source : Source) :
    Scheduled.goalFreeWithin (footprint environment source) (sourceGoal environment source) := by
  intro name member
  exact List.mem_append_right _ member

theorem start_returns (state : Effects.State) (environment : Environment) (source : Source)
    (finiteProvider : environment.provider.dynamicRelations = []) (fuel : Nat) :
    PureReturns descentLibrary.runtime [] state (startCode environment source fuel) state
      (encoded (observe environment source
        (Scheduled.resume environment source.bound source.type source.term fuel
          (Scheduled.begin environment source.bound source.type source.term))).term) := by
  have runs := descent_run_from_start_returns state environment finiteProvider
    (footprint environment source) (provider_within environment source)
    (sourceGoal environment source) (goal_within environment source) fuel
  exact readout_returns state environment source _ _ runs

/-- The retained certified scheduler state stays inside the computed finite
name footprint, including fixed provider outputs. -/
theorem session_within (installed : BindingPipeline.Installed) (source : Source)
    (finiteProvider : installed.Environment.provider.dynamicRelations = [])
    (session : BindingPipeline.Installed.CertifiedExecution.Session installed source) :
    Scheduled.stateFreeWithin (footprint installed.Environment source) installed.Environment
      (sourceGoal installed.Environment source) session.state := by
  rw [session.replay]
  exact Scheduled.run_free_within _ _ _
    (provider_coverage_mono _ _ _ (provider_within installed.Environment source)
      (provider_covered_by_own_names _))
    (Query.DynamicOutputsFreeWithin.of_unregistered _ _ finiteProvider)
    session.budget _ (Scheduled.start_free_within _ _ _ (goal_within installed.Environment source))

theorem resume_returns (state : Effects.State) (installed : BindingPipeline.Installed) (source : Source)
    (finiteProvider : installed.Environment.provider.dynamicRelations = [])
    (session : BindingPipeline.Installed.CertifiedExecution.Session installed source) (fuel : Nat) :
    PureReturns descentLibrary.runtime [] state
      (resumeCode installed.Environment source (stateTerm session.state) fuel) state
      (encoded (observe installed.Environment source (session.resume fuel).state).term) := by
  have runs := descent_run_returns state installed.Environment finiteProvider
    (footprint installed.Environment source) (provider_within installed.Environment source)
    (sourceGoal installed.Environment source) fuel session.state
    (session_within installed source finiteProvider session)
  exact readout_returns state installed.Environment source _ _ runs

/-- The target evaluation cannot publish an additional answer or substitute
a different packet: every completed result is exactly the specified readout. -/
theorem resume_completed_iff (before : Effects.State) (installed : BindingPipeline.Installed)
    (source : Source) (finiteProvider : installed.Environment.provider.dynamicRelations = [])
    (session : BindingPipeline.Installed.CertifiedExecution.Session installed source) (fuel : Nat)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ targetFuel, Eval.run descentLibrary.runtime targetFuel
      {state := before, control := .evaluate []
        (resumeCode installed.Environment source (stateTerm session.state) fuel)} =
        .complete after answers input output) ↔
      after = before ∧
        answers = [encoded (observe installed.Environment source (session.resume fuel).state).term] ∧
        input = [] ∧ output = [] :=
  path_completed_iff descentLibrary.runtime _ before _ [] []
    (resume_returns before installed source finiteProvider session fuel) after answers input output

theorem start_completed_iff (before : Effects.State) (environment : Environment) (source : Source)
    (finiteProvider : environment.provider.dynamicRelations = []) (fuel : Nat)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ targetFuel, Eval.run descentLibrary.runtime targetFuel
      {state := before, control := .evaluate [] (startCode environment source fuel)} =
        .complete after answers input output) ↔
      after = before ∧
        answers = [encoded (observe environment source
          (Scheduled.resume environment source.bound source.type source.term fuel
            (Scheduled.begin environment source.bound source.type source.term))).term] ∧
        input = [] ∧ output = [] :=
  path_completed_iff descentLibrary.runtime _ before _ [] []
    (start_returns before environment source finiteProvider fuel) after answers input output

theorem resume_decode (state : Effects.State) (installed : BindingPipeline.Installed)
    (source : Source) (finiteProvider : installed.Environment.provider.dynamicRelations = [])
    (session : BindingPipeline.Installed.CertifiedExecution.Session installed source) (fuel : Nat) :
    ∃ result, PureReturns descentLibrary.runtime [] state
      (resumeCode installed.Environment source (stateTerm session.state) fuel) state result ∧
      decodeAtom? result = some (observe installed.Environment source (session.resume fuel).state) :=
  ⟨_, resume_returns state installed source finiteProvider session fuel, decodeAtom?_encoded _⟩

theorem observe_resume_add (installed : BindingPipeline.Installed) (source : Source)
    (session : BindingPipeline.Installed.CertifiedExecution.Session installed source) (first extra : Nat) :
    observe installed.Environment source (session.resume (first + extra)).state =
      observe installed.Environment source ((session.resume first).resume extra).state := by
  rw [session.resume_add]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.SourceExecution
