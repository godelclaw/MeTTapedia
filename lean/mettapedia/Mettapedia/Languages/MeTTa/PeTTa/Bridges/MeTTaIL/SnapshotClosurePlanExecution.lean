import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureProviderTyping

/-! Installing an immutable fact snapshot validates its rows and retains
the compiled code, typed free context, equation data and descent check. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

private def planTerm (prepared : Executable.Prepared) (known : List Pattern) : Term :=
  CompletePlanWire.planTerm (Executable.plan prepared known) (Executable.freeTypes prepared.vocabulary)
    [] (.base "DlStatement")

private theorem plan_snapshot (prepared : Executable.Prepared) (known : List Pattern) :
    (Executable.plan prepared known).snapshot = Executable.snapshot prepared known := rfl

private theorem plan_permissions (prepared : Executable.Prepared) (known : List Pattern) :
    (Executable.plan prepared known).permissions = Executable.permissions := rfl

theorem append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left),encoded (encodeList element right)]) state
      (encoded (encodeList element (left ++ right))) := by
  have runner := runner_from_base% ["left","right"]
    (CompleteExecution.complete_append_returns element state left right) using RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift checked ["left","right"] runner

private theorem equation_terms_stable (prepared : Executable.Prepared) (before after : List Pattern) :
    encodeList (CompletePlanWire.equationDeclarationTerm (Executable.plan prepared after))
      (Executable.plan prepared after).equations.zipIdx =
    encodeList (CompletePlanWire.equationDeclarationTerm (Executable.plan prepared before))
      (Executable.plan prepared before).equations.zipIdx := by
  rw [← Executable.snapshot_equations_stable prepared before after]
  have same : CompletePlanWire.equationDeclarationTerm (Executable.plan prepared after) =
      CompletePlanWire.equationDeclarationTerm (Executable.plan prepared before) := by
    funext pair
    unfold CompletePlanWire.equationDeclarationTerm CompletePlanWire.equationDepthTerm
    rw [Executable.snapshot_descent_stable prepared before after]
  rw [same]

private theorem plan_after_shape (prepared : Executable.Prepared) (before after : List Pattern) :
    planTerm prepared after = .application "CompletePlan"
      [PremiseOperationsExecution.GeneralExecution.environmentTerm
         {GeneralPlanEnvironment.environment (Executable.plan prepared before) with
           provider := (Executable.snapshot prepared after).provider}
         (Executable.freeTypes prepared.vocabulary),
       InferenceCettaWire.ContextObservation.permissionsTerm Executable.permissions.sites,
       encodeList InferenceCettaWire.AuthoredRule.typeTerm [],
       InferenceCettaWire.AuthoredRule.typeTerm (.base "DlStatement"),
       encodeList ScopedRuleJobReadoutExecution.rulePlanTerm (Executable.plan prepared before).rules,
       encodeList (CompletePlanWire.equationDeclarationTerm (Executable.plan prepared before))
         (Executable.plan prepared before).equations.zipIdx,
       CompletePlanWire.admittedTerm (StructuralDescent.checkEnvironment
         (GeneralPlanEnvironment.environment (Executable.plan prepared before)))] := by
  unfold planTerm CompletePlanWire.planTerm
  rw [equation_terms_stable prepared before after,
    ← Executable.snapshot_rules_stable prepared before after,
    Executable.snapshot_descent_stable prepared before after,
    Executable.snapshot_environment_transport prepared before after]
  rfl

theorem plan_returns (state : State) (prepared : Executable.Prepared) (before after : List Pattern) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:plan" [encoded (planTerm prepared before),encoded (.string Query.factRelation),
        encoded (factsTerm after),encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows)])
      state (encoded (encodeOption id
        (if ClosureMachine.closed prepared after then some (planTerm prepared after) else none))) := by
  have rows := rows_returns state Query.factRelation after
  have joined := append_returns PremiseOperationsExecution.GeneralExecution.providerRowTerm state
    (Query.provider after).rows prepared.staticRows
  have checkedRows := snapshot_check_rows_returns state prepared after
  cases valid : ClosureMachine.closed prepared after <;>
    (rw [valid] at checkedRows
     simp only [Bool.false_eq_true,if_false,if_true]
     try rw [plan_after_shape prepared before after]
     metta_call checked
     metta_eval [rows,joined,checkedRows] with checked unfolding
       [planTerm,CompletePlanWire.planTerm,
        PremiseOperationsExecution.GeneralExecution.environmentTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm,
        plan_snapshot,plan_permissions,Executable.snapshot,GeneralPlanEnvironment.environment,
        Query.provider,rowsTerm,factsTerm,encodeList_map])

#print axioms equation_terms_stable
#print axioms plan_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
