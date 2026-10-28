import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureKeyExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosurePremiseExecution

/-! Native firing readback preserves the source statement position,
grounding, positive premises and target from the retained receipt. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem firing_returns (state : State) (prepared : Executable.Prepared) (facts : List Pattern)
    (receipt : GeneralOccurrenceSemantics.Receipt) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:firing" [encoded (ClosureMachine.metadataTerm prepared),encoded (factsTerm facts),
        encoded (CompleteExecution.classReceiptTerm receipt)]) state
      (encoded (encodeOption (fun key => .application "SnapshotFiring"
        [ClosureMachine.keyTerm key,InferenceCettaWire.encodePattern receipt.target])
        (ClosureMachine.key? prepared facts receipt))) := by
  let clauseTerm : Nat × Clause → Term := fun (ordinal,clause) =>
    .application "SnapshotClause" [.natural ordinal,
      encodeList (fun name => .application "SnapshotVariable" [.string name,.string (Join.logicalVariable name)])
        (DerivationIdentity.clauseVariables clause),.natural clause.positiveAtoms.length]
  have picked := row_returns clauseTerm state receipt.firing.job.declaration.declarationIndex
    (LPBridge.numberedClauses prepared.source)
  cases selected : (LPBridge.numberedClauses prepared.source)[receipt.firing.job.declaration.declarationIndex]? with
  | none =>
    rw [selected] at picked
    simp [ClosureMachine.key?,selected]
    metta_call checked
    metta_eval [picked] with checked unfolding [clauseTerm,ClosureMachine.metadataTerm,factsTerm,
      CompleteExecution.classReceiptTerm,ScopedRuleJobReadoutExecution.receiptTerm,
      ScopedRuleJobReadoutExecution.jobTerm,ScopedRuleJobReadoutExecution.rulePlanTerm]
  | some entry =>
    rcases entry with ⟨ordinal,clause⟩
    rw [selected] at picked
    have grounding := grounding_returns state (DerivationIdentity.clauseVariables clause) receipt.firing.completed
    cases grounded : ClosureMachine.grounding? (DerivationIdentity.clauseVariables clause) receipt.firing.completed with
    | none =>
      rw [grounded] at grounding
      simp [ClosureMachine.key?,selected,grounded]
      metta_call checked
      metta_eval [picked,grounding] with checked unfolding [clauseTerm,ClosureMachine.metadataTerm,factsTerm,
        CompleteExecution.classReceiptTerm,ScopedRuleJobReadoutExecution.receiptTerm,
        ScopedRuleJobReadoutExecution.jobTerm,ScopedRuleJobReadoutExecution.rulePlanTerm]
    | some bindings =>
      rw [grounded] at grounding
      have premises := premises_returns state clause.positiveAtoms.length receipt.firing.premiseHistory facts
      cases positive : ClosureMachine.premiseFacts? clause.positiveAtoms.length receipt.firing.premiseHistory facts <;>
        (rw [positive] at premises
         simp [ClosureMachine.key?,selected,grounded,positive]
         metta_call checked
         metta_eval [picked,grounding,premises] with checked unfolding [clauseTerm,
           ClosureMachine.metadataTerm,ClosureMachine.keyTerm,factsTerm,GeneralOccurrenceSemantics.Receipt.target,
           CompleteExecution.classReceiptTerm,ScopedRuleJobReadoutExecution.receiptTerm,
           ScopedRuleJobReadoutExecution.jobTerm,ScopedRuleJobReadoutExecution.rulePlanTerm])

#print axioms firing_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
