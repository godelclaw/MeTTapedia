import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Deepening
import Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Sizes
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution

/-!
# The deepening family of a rule job

A rule job deepens over its rule's root goal at the job's focus. Its MeTTa data is
`(RootFamily bound type focus ordinal admitted)`, where `admitted` says whether the plan passes the
structural admission check, which bounds every derivation by the focus size. Its payloads are
firings, written as the descent machine's root answers.
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

/-- A firing, as the descent machine's root answer writes it. -/
def firingTerm (firing : Complete.DeepRoot.Firing) : Term :=
  .application "RootAnswer" [PremiseOperationsExecution.GeneralExecution.traceTerm firing.trace,
    assignmentTerm firing.captured, assignmentTerm firing.completed,
    PremiseOperationsExecution.GeneralExecution.eventsTerm firing.history, patternTerm firing.target]

def decodeFiring? : Term → Option Complete.DeepRoot.Firing
  | .application "RootAnswer" [trace, captured, completed, history, target] => do
      pure ⟨← ScopedRuleJobReadoutExecution.decodeTrace? trace, ← ScopedRuleJobReadoutExecution.decodeAssignment? captured,
        ← ScopedRuleJobReadoutExecution.decodeAssignment? completed, ← ScopedRuleJobReadoutExecution.decodeEvents? history,
        ← InferenceCettaWire.decodePattern target⟩
  | _ => none

theorem decodeFiring?_firingTerm (firing : Complete.DeepRoot.Firing) : decodeFiring? (firingTerm firing) = some firing := by
  obtain ⟨trace, captured, completed, history, target⟩ := firing
  simp [firingTerm, decodeFiring?, assignmentTerm, patternTerm,
    ScopedRuleJobReadoutExecution.decodeAssignment?_assignmentTerm]

theorem firingTerm_injective : Function.Injective firingTerm := by
  intro first second same
  have decoded := congrArg decodeFiring? same
  simpa only [decodeFiring?_firingTerm, Option.some.injEq] using decoded

/-- Preserve the selected choice representation in a complete firing payload. -/
def firingTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (firing : Complete.DeepRoot.Firing Choice) : Term :=
  .application "RootAnswer" [encodeList choiceTerm firing.trace,
    assignmentTerm firing.captured, assignmentTerm firing.completed,
    RetainedMatchingWire.eventsTerm choiceTerm firing.history, patternTerm firing.target]

def decodeFiringWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (Complete.DeepRoot.Firing Choice)
  | .application "RootAnswer" [trace, captured, completed, history, target] => do
      pure ⟨← decodeList decodeChoice trace, ← ScopedRuleJobReadoutExecution.decodeAssignment? captured,
        ← ScopedRuleJobReadoutExecution.decodeAssignment? completed,
        ← ScopedRuleJobReadoutExecution.decodeEventsWith? decodeChoice history,
        ← InferenceCettaWire.decodePattern target⟩
  | _ => none

theorem decodeFiringWith?_firingTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (firing : Complete.DeepRoot.Firing Choice) :
    decodeFiringWith? decodeChoice (firingTermWith choiceTerm firing) = some firing := by
  rcases firing with ⟨trace, captured, completed, history, target⟩
  simp [firingTermWith, decodeFiringWith?, assignmentTerm, patternTerm,
    ScopedRuleJobReadoutExecution.decodeAssignment?_assignmentTerm,
    ScopedRuleJobReadoutExecution.decodeEventsWith?_eventsTerm choiceTerm decodeChoice inverse,
    decodeList_encodeList decodeChoice choiceTerm inverse]

theorem firingTermWith_injective {Choice : Type} (choiceTerm : Choice → Term)
    (decodeChoice : Term → Option Choice) (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (firingTermWith choiceTerm) := by
  intro first second same
  have decoded := congrArg (decodeFiringWith? decodeChoice) same
  simpa only [decodeFiringWith?_firingTermWith choiceTerm decodeChoice inverse, Option.some.injEq] using decoded

theorem firingTermWith_ordinary (firing : Complete.DeepRoot.Firing) :
    firingTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm firing = firingTerm firing := by
  unfold firingTermWith firingTerm
  rw [RetainedMatchingWire.ordinary_events]
  rfl

theorem decodeFiringWith?_wrong_constructor {Choice : Type} (decodeChoice : Term → Option Choice) :
    decodeFiringWith? decodeChoice (.application "RuleJobReceipt" []) = none := rfl

#print axioms decodeFiringWith?_firingTermWith
#print axioms firingTermWith_injective
#print axioms firingTermWith_ordinary
#print axioms decodeFiringWith?_wrong_constructor


/-- The data of a rule's deepening at a focus. -/
def rootFamilyTerm (request : Complete.DeepRoot.Request) : Term :=
  .application "RootFamily" [encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound,
    InferenceCettaWire.AuthoredRule.typeTerm request.type, InferenceCettaWire.encodePattern request.source,
    .natural request.index, CompletePlanWire.admittedTerm (StructuralDescent.checkEnvironment request.environment)]

/-- Comparing a value with a literal symbol. -/
theorem symbol_equal_returns (program : SpaceSemantics.Program) (caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (state : State) (left : Atom) (other name : String)
    (leftReturns : PureReturns program caller state left state (.symbol other)) :
    PureReturns program caller state (apply "==" [left, .symbol name]) state (Effects.boolean (decide (other = name))) := by
  have compared := term_equal_returns program caller state left (.symbol name) (.symbol other) (.symbol name)
    leftReturns (Eval.symbol_returns program caller state name)
  simpa only [Term.symbol.injEq] using compared

@[metta_head "gslt:deep:goal"]
theorem root_goal_returns (request : Complete.DeepRoot.Request) (state : State) (depth : Nat) :
    PureReturns runtime [] state (apply "gslt:deep:goal" [encoded (rootFamilyTerm request), number depth]) state
      (encoded (goalTerm ((Complete.DeepRoot.family request).goal depth))) := by
  metta_call_in completeProof_checked using completeProof_agreement
  metta_eval with completeProof_checked in completeProof_agreement unfolding [rootFamilyTerm, goalTerm, Complete.DeepRoot.Request.goal, typesTerm, typeTerm, patternTerm,
    CompletePlanWire.admittedTerm]

@[metta_head "gslt:deep:bounded"]
theorem root_bounded_returns (request : Complete.DeepRoot.Request) (state : State) (depth : Nat) :
    PureReturns runtime [] state (apply "gslt:deep:bounded" [encoded (rootFamilyTerm request), number depth]) state
      (Effects.boolean (match (Complete.DeepRoot.family request).bound with
        | some limit => decide (limit ≤ depth)
        | none => false)) := by
  have size := nodes_returns state request.source
  cases admitted : StructuralDescent.checkEnvironment request.environment
  · have unbounded : (Complete.DeepRoot.family request).bound = none := by
      simp [admitted]
    rw [unbounded]
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rootFamilyTerm, CompletePlanWire.admittedTerm, admitted]
    apply pure_if_returns
    · exact symbol_equal_returns _ _ _ _ "Unadmitted" "Admitted" (bound_returns _ _ _ (by rfl))
    · simp only [show decide ("Unadmitted" = "Admitted") = false by decide, Bool.false_eq_true, ↓reduceIte]
      metta_eval with completeProof_checked in completeProof_agreement
  · have bounded : (Complete.DeepRoot.family request).bound = some (PatternTreeSize.nodes request.source) := by
      simp [admitted]
    rw [bounded]
    metta_call_in completeProof_checked using completeProof_agreement
    metta_eval with completeProof_checked in completeProof_agreement unfolding [rootFamilyTerm, CompletePlanWire.admittedTerm, admitted]
    apply pure_if_returns
    · exact symbol_equal_returns _ _ _ _ "Admitted" "Admitted" (bound_returns _ _ _ (by rfl))
    · simp only
      metta_eval [size] with completeProof_checked in completeProof_agreement unfolding [patternValue]

/-- A rule's deepening at a focus, as MeTTa data. -/
def rootWire (request : Complete.DeepRoot.Request) : FamilyWire (Complete.DeepRoot.family request) where
  term := rootFamilyTerm request
  payload := firingTerm
  injective := firingTerm_injective
  answer result := by cases result; rfl
  goal := root_goal_returns request
  bounded := root_bounded_returns request

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.firingTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.decodeFiring?

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.decodeFiring?_firingTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.firingTerm_injective

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.firingTermWith

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.decodeFiringWith?

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.decodeFiringWith?_firingTermWith

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.firingTermWith_injective

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.firingTermWith_ordinary

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.decodeFiringWith?_wrong_constructor

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.rootFamilyTerm

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.symbol_equal_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.root_goal_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.root_bounded_returns

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.rootWire
