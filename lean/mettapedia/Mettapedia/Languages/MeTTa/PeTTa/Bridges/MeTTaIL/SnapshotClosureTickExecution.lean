import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureCommitExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureSearchExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureInvariant

/-! One native tick preserves the full retained closure state, including
pending work, completed publications, logical keys and provider faults. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval BridgeKit WireKit
open Complete.Footprint

private theorem status_captured_returns (state : State) (prepared : Executable.Prepared) (facts : List Pattern)
    (run : Complete.Classes.State (Executable.plan prepared facts))
    (ready : CompleteExecution.SearchReady [] (.base "DlStatement")
      (Complete.Footprint.declaredFootprint (Executable.plan prepared facts)) run) (caller : Subst)
    (rp : applySubst caller (.var "plan") = encoded (CompletePlanWire.planTerm (Executable.plan prepared facts)
      (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")))
    (rr : applySubst caller (.var "advanced") = encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts) run)) :
    PureReturns runtime caller state
      (apply "gslt:search:status" [.symbol "ClassSearch",.var "plan",.var "advanced"]) state
      (CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared facts).status run)) := by
  have status := search_status_returns state prepared facts run ready
  refine PureData.raw_capture_returns runtime [] caller state state "gslt:search:status"
    [CompleteExecution.classSearchBackend,
      encoded (CompletePlanWire.planTerm (Executable.plan prepared facts) (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
      encoded (CompleteExecution.classStateTerm (Executable.plan prepared facts) run)]
    [.symbol "ClassSearch",.var "plan",.var "advanced"] _ ?_ ?_ ?_ ?_ status
  · decide +kernel
  · intro index bounded
    simp only [List.length_cons,List.length_nil,Nat.zero_add] at bounded
    revert index
    decide +kernel
  · decide
  · simp only [List.map_cons,List.map_nil,encoded,CompleteExecution.classSearchBackend,CettaWireAtom.applySubst_encode]
    change _ = .symbol "ClassSearch" :: [applySubst caller (.var "plan"),applySubst caller (.var "advanced")]
    rw [rp,rr]
    rfl

theorem tick_returns (state : State) (prepared : Executable.Prepared) (before : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true)
    (machine : ClosureMachine.Machine prepared) (ready : ClosureMachine.Ready prepared machine) (quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:tick" [encoded (ClosureMachine.machineTerm prepared machine),number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared (ClosureMachine.tick prepared machine quantum))) := by
  cases fault : machine.fault with
  | some failure =>
    rw [ClosureMachine.stopped_tick prepared machine quantum (Or.inr (by simp [fault]))]
    cases failure <;>
      (metta_call checked
       metta_eval with checked unfolding [ClosureMachine.machineTerm,fault])
  | none =>
    cases finished : machine.complete with
    | true =>
      rw [ClosureMachine.stopped_tick prepared machine quantum (Or.inl finished)]
      metta_call checked
      metta_eval with checked unfolding [ClosureMachine.machineTerm,fault,finished]
    | false =>
      obtain ⟨closed,searchReady⟩ := ready fault
      let advanced := (ClosureMachine.search prepared machine.facts).resume machine.run quantum
      have advancedReady := CompleteExecution.searchReady_rounds
        (ClosureMachine.admitted_scope prepared before machine.facts admitted closed).1 quantum searchReady
      have resumed := search_resume_returns state prepared before machine.facts admitted closed machine.run searchReady quantum
      have publication := search_publication_returns state prepared machine.facts advanced
      cases outcome : (ClosureMachine.search prepared machine.facts).status advanced with
      | pending =>
        have notDone : ((ClosureMachine.search prepared machine.facts).status
            ((ClosureMachine.search prepared machine.facts).resume machine.run quantum) != .complete) = true := by
          change ((ClosureMachine.search prepared machine.facts).status advanced != .complete) = true
          rw [outcome]
          decide
        simp only [ClosureMachine.tick,finished,fault,Bool.false_or,Option.isSome_none,
          Bool.false_eq_true,if_false,notDone,if_true]
        metta_call checked
        metta_eval [resumed] with checked unfolding [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced]
        apply pure_if_returns
        · apply CompleteExecution.symbol_equal_returns _ _ _ _ "SearchPending" "SearchComplete"
          have result : CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared machine.facts).status advanced) =
              OSLFCore.Atom.symbol "SearchPending" := by
            rw [outcome]
            rfl
          rw [← result]
          apply status_captured_returns state prepared machine.facts advanced advancedReady
          · rfl
          · rfl
        · simp only [show decide ("SearchPending" = "SearchComplete") = false from rfl,Bool.false_eq_true,if_false]
          metta_eval with checked unfolding [ClosureMachine.machineTerm,fault,finished]
      | blocked =>
        have impossible : (ClosureMachine.search prepared machine.facts).status advanced ≠ .blocked := by
          simp only [ClosureMachine.search,Complete.Normalized.search,Complete.Classes.search,Complete.Classes.status]
          split <;> decide
        exact (impossible outcome).elim
      | complete =>
        have done : ((ClosureMachine.search prepared machine.facts).status
            ((ClosureMachine.search prepared machine.facts).resume machine.run quantum) != .complete) = false := by
          change ((ClosureMachine.search prepared machine.facts).status advanced != .complete) = false
          rw [outcome]
          decide
        obtain ⟨published,committed⟩ := commit_returns state prepared machine.facts
          ((ClosureMachine.search prepared machine.facts).publication advanced) machine.facts machine.keys []
        cases commit : ClosureMachine.commit? prepared machine.facts
            ((ClosureMachine.search prepared machine.facts).publication advanced) machine.facts machine.keys with
        | none =>
          rw [commit] at committed
          change PureReturns runtime [] state _ state (encoded (.symbol "None")) at committed
          simp only [ClosureMachine.tick,finished,fault,Bool.false_or,Option.isSome_none,
            Bool.false_eq_true,if_false,done]
          simp only [show ClosureMachine.commit? prepared machine.facts
            ((ClosureMachine.search prepared machine.facts).publication
              ((ClosureMachine.search prepared machine.facts).resume machine.run quantum)) machine.facts machine.keys = _ from commit]
          metta_call checked
          metta_eval [resumed] with checked unfolding [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced]
          apply pure_if_returns
          · apply CompleteExecution.symbol_equal_returns _ _ _ _ "SearchComplete" "SearchComplete"
            have result : CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared machine.facts).status advanced) =
                OSLFCore.Atom.symbol "SearchComplete" := by
              rw [outcome]
              rfl
            rw [← result]
            apply status_captured_returns state prepared machine.facts advanced advancedReady
            · rfl
            · rfl
          · metta_eval [publication,committed] with checked unfolding
              [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced,factsTerm]
        | some next =>
          rcases next with ⟨facts,keys⟩
          rw [commit] at committed
          change PureReturns runtime [] state _ state
            (encoded (.application "Some" [.application "SnapshotCommit"
              [factsTerm facts,encodeList ClosureMachine.keyTerm keys,encodeList ClosureMachine.keyTerm published]])) at committed
          have history := append_returns ClosureMachine.epochTerm state machine.history
            [⟨machine.round,machine.facts,(ClosureMachine.search prepared machine.facts).publication advanced⟩]
          by_cases same : facts = machine.facts
          · subst facts
            simp only [ClosureMachine.tick,finished,fault,Bool.false_or,Option.isSome_none,
              Bool.false_eq_true,if_false,done]
            simp only [show ClosureMachine.commit? prepared machine.facts
              ((ClosureMachine.search prepared machine.facts).publication
                ((ClosureMachine.search prepared machine.facts).resume machine.run quantum)) machine.facts machine.keys = _ from commit,
              ↓reduceIte]
            metta_call checked
            metta_eval [resumed] with checked unfolding [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced]
            apply pure_if_returns
            · apply CompleteExecution.symbol_equal_returns _ _ _ _ "SearchComplete" "SearchComplete"
              have result : CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared machine.facts).status advanced) =
                  OSLFCore.Atom.symbol "SearchComplete" := by
                rw [outcome]
                rfl
              rw [← result]
              apply status_captured_returns state prepared machine.facts advanced advancedReady
              · rfl
              · rfl
            · metta_eval [publication,committed,history] with checked unfolding
                [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced,factsTerm,ClosureMachine.epochTerm]
          · have different : encodeList InferenceCettaWire.encodePattern machine.facts ≠
                encodeList InferenceCettaWire.encodePattern facts := by
              intro equal
              exact same ((encodeList_injective _ InferenceCettaWire.encodePattern_injective equal).symm)
            have plan := plan_returns state prepared machine.facts facts
            cases nextClosed : ClosureMachine.closed prepared facts with
            | false =>
              rw [nextClosed] at plan
              change PureReturns runtime [] state
                (apply "gslt:snapshot:plan"
                  [encoded (CompletePlanWire.planTerm (Executable.plan prepared machine.facts)
                    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
                   encoded (.string Query.factRelation),encoded (factsTerm facts),
                   encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows)]) state
                (encoded (.symbol "None")) at plan
              simp only [ClosureMachine.tick,finished,fault,Bool.false_or,Option.isSome_none,
                Bool.false_eq_true,if_false,done]
              simp only [show ClosureMachine.commit? prepared machine.facts
                ((ClosureMachine.search prepared machine.facts).publication
                  ((ClosureMachine.search prepared machine.facts).resume machine.run quantum)) machine.facts machine.keys = _ from commit,
                same,if_false,nextClosed,Bool.false_eq_true]
              metta_call checked
              metta_eval [resumed] with checked unfolding [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced]
              apply pure_if_returns
              · apply CompleteExecution.symbol_equal_returns _ _ _ _ "SearchComplete" "SearchComplete"
                have result : CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared machine.facts).status advanced) =
                    OSLFCore.Atom.symbol "SearchComplete" := by
                  rw [outcome]
                  rfl
                rw [← result]
                apply status_captured_returns state prepared machine.facts advanced advancedReady
                · rfl
                · rfl
              · metta_eval [publication,committed,history] with checked unfolding
                  [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced,factsTerm,ClosureMachine.epochTerm]
                simp only [if_neg different]
                metta_eval [plan] with checked unfolding [ClosureMachine.machineTerm]
            | true =>
              rw [nextClosed] at plan
              change PureReturns runtime [] state
                (apply "gslt:snapshot:plan"
                  [encoded (CompletePlanWire.planTerm (Executable.plan prepared machine.facts)
                    (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
                   encoded (.string Query.factRelation),encoded (factsTerm facts),
                   encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows)]) state
                (encoded (.application "Some" [CompletePlanWire.planTerm (Executable.plan prepared facts)
                  (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")])) at plan
              have search := search_zero_returns state prepared before facts admitted nextClosed
              simp only [ClosureMachine.tick,finished,fault,Bool.false_or,Option.isSome_none,
                Bool.false_eq_true,if_false,done]
              simp only [show ClosureMachine.commit? prepared machine.facts
                ((ClosureMachine.search prepared machine.facts).publication
                  ((ClosureMachine.search prepared machine.facts).resume machine.run quantum)) machine.facts machine.keys = _ from commit,
                same,if_false,nextClosed,if_true]
              metta_call checked
              metta_eval [resumed] with checked unfolding [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced]
              apply pure_if_returns
              · apply CompleteExecution.symbol_equal_returns _ _ _ _ "SearchComplete" "SearchComplete"
                have result : CompleteExecution.searchStatusAtom ((ClosureMachine.search prepared machine.facts).status advanced) =
                    OSLFCore.Atom.symbol "SearchComplete" := by
                  rw [outcome]
                  rfl
                rw [← result]
                apply status_captured_returns state prepared machine.facts advanced advancedReady
                · rfl
                · rfl
              · metta_eval [publication,committed,history] with checked unfolding
                  [ClosureMachine.machineTerm,fault,finished,CompleteExecution.classSearchBackend,advanced,factsTerm,ClosureMachine.epochTerm]
                simp only [if_neg different]
                metta_eval [plan,search] with checked unfolding
                  [ClosureMachine.machineTerm,CompleteExecution.classSearchBackend,advanced,factsTerm,ClosureMachine.epochTerm]

#print axioms tick_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
