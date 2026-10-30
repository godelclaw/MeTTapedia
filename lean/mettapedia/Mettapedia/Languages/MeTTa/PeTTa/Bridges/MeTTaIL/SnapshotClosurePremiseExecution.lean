import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosurePlanExecution

/-! Positive-premise readback resolves recorded row positions against the
same immutable fact snapshot. Out-of-range rows and nested events fail
explicitly instead of manufacturing a premise fact. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem row_returns {α : Type} (element : α → Term) (state : State) (index : Nat) (items : List α) :
    PureReturns runtime [] state
      (apply "gslt:rule:row-at" [number index,encoded (encodeList element items)]) state
      (encoded (encodeOption element items[index]?)) := by
  have common := CompleteExecution.descent_row_returns element state index items
  have runner := runner_from_base% ["index","items"] common using RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift checked ["index","items"] runner

theorem premises_returns (state : State) (count : Nat) (events : List GeneralPremise.Event) (facts : List Pattern) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:premises" [number count,
        encoded (PremiseOperationsExecution.GeneralExecution.eventsTerm events),encoded (factsTerm facts)]) state
      (encoded (encodeOption (encodeList InferenceCettaWire.encodePattern)
        (ClosureMachine.premiseFacts? count events facts))) := by
  induction count generalizing events with
  | zero =>
    metta_call checked
    metta_eval with checked unfolding [ClosureMachine.premiseFacts?]
  | succ count ih =>
    cases events with
    | nil =>
      metta_call checked
      metta_eval with checked unfolding [ClosureMachine.premiseFacts?,
        PremiseOperationsExecution.GeneralExecution.eventsTerm]
    | cons event rest =>
      cases event with
      | query index quantifiers row origins =>
        cases quantifiers with
        | zero =>
          have picked := row_returns InferenceCettaWire.encodePattern state row facts
          cases found : facts[row]? with
          | none =>
            rw [found] at picked
            simp only [ClosureMachine.premiseFacts?,bne_self_eq_false,found]
            metta_call checked
            metta_eval [picked] with checked unfolding [factsTerm,
              PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm]
          | some fact =>
            rw [found] at picked
            have tail := ih rest
            cases read : ClosureMachine.premiseFacts? count rest facts <;>
              (rw [read] at tail
               simp only [ClosureMachine.premiseFacts?,bne_self_eq_false,found,read]
               metta_call checked
               metta_eval [picked,tail] with checked unfolding [factsTerm,
                 PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm])
        | succ depth =>
          metta_call checked
          metta_eval with checked unfolding [ClosureMachine.premiseFacts?,factsTerm,
            PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm]
      | freshness index quantifiers atom subject =>
        metta_call checked
        metta_eval with checked unfolding [ClosureMachine.premiseFacts?,factsTerm,
          PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm]
      | quantified index quantifiers kind elements =>
        metta_call checked
        metta_eval with checked unfolding [ClosureMachine.premiseFacts?,factsTerm,
          PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm]
      | child index quantifiers declaration bound source target trace targetTrace captured completed history =>
        metta_call checked
        metta_eval with checked unfolding [ClosureMachine.premiseFacts?,factsTerm,
          PremiseOperationsExecution.GeneralExecution.eventsTerm,PremiseOperationsExecution.GeneralExecution.eventTerm]

#print axioms row_returns
#print axioms premises_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
