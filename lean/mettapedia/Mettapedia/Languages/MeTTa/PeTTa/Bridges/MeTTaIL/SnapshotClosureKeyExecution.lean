import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosurePlanExecution

/-! Receipt readback retains the original contextual assignment. Only
captures with empty dependency and ambient contexts can become Datalog
grounding values. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval BridgeKit WireKit

private theorem dependencies_test_returns (caller : Subst) (state : State) (dependencies : List TypeExpr)
    (read : applySubst caller (.var "dependencies") =
      encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies)) :
    PureReturns runtime caller state (apply "==" [.var "dependencies",.symbol "LNil"]) state
      (Effects.boolean dependencies.isEmpty) := by
  have left := variable_returns runtime caller state "dependencies"
  rw [read] at left
  have right := Eval.symbol_returns runtime caller state "LNil"
  have same := term_equal_returns runtime caller state (.var "dependencies") (.symbol "LNil")
    (encodeList InferenceCettaWire.AuthoredRule.typeTerm dependencies) (.symbol "LNil") left right
  cases dependencies <;> simpa [encodeList] using same

private def bindingResult (name : String) (assignment : ScopedRuleMatching.Assignment) : Option Pattern := do
  let value ← ScopedRuleMatching.lookup assignment name
  if value.dependencies.isEmpty && value.ambient == 0 then some value.body else none

theorem binding_returns (state : State) (name : String) (assignment : ScopedRuleMatching.Assignment) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:binding" [encoded (.string name),
        encoded (CompleteExecution.DescentCodec.assignmentTerm assignment)]) state
      (encoded (encodeOption InferenceCettaWire.encodePattern (bindingResult name assignment))) := by
  induction assignment with
  | nil =>
    metta_call checked
    metta_eval with checked unfolding [bindingResult,ScopedRuleMatching.lookup,
      CompleteExecution.DescentCodec.assignmentTerm,RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm,MatchAutomataBindingExecution.payloadBindingTerm]
  | cons entry rest ih =>
    rcases entry with ⟨other,value⟩
    by_cases same : name = other
    · subst other
      cases value with
      | mk dependencies ambient body =>
        cases dependencies with
        | nil =>
          cases ambient <;>
            (simp [bindingResult,ScopedRuleMatching.lookup,List.find?]
             metta_call checked
             metta_eval with checked unfolding [bindingResult,ScopedRuleMatching.lookup,
               CompleteExecution.DescentCodec.assignmentTerm,RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
               MatchAutomataBindingExecution.payloadBindingsTerm,MatchAutomataBindingExecution.payloadBindingTerm,InferenceCettaWire.AuthoredRule.contextualValueTerm,InferenceCettaWire.encodeList]
             apply pure_if_returns
             · exact dependencies_test_returns _ state [] rfl
             · simp only [List.isEmpty_nil,if_true]
               metta_eval with checked)
        | cons dependency dependencies =>
          simp [bindingResult,ScopedRuleMatching.lookup,List.find?]
          metta_call checked
          metta_eval with checked unfolding [bindingResult,ScopedRuleMatching.lookup,
            CompleteExecution.DescentCodec.assignmentTerm,RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
            MatchAutomataBindingExecution.payloadBindingsTerm,MatchAutomataBindingExecution.payloadBindingTerm,InferenceCettaWire.AuthoredRule.contextualValueTerm,InferenceCettaWire.encodeList]
          apply pure_if_returns
          · exact dependencies_test_returns _ state (dependency :: dependencies) rfl
          · simp only [List.isEmpty_cons]
            metta_eval with checked
    · have different : other ≠ name := Ne.symm same
      have unequal : (other == name) = false := beq_eq_false_iff_ne.mpr different
      simp only [bindingResult,ScopedRuleMatching.lookup,List.find?_cons,unequal,Option.map]
      metta_call checked
      metta_eval [ih] with checked unfolding [same,different,
        CompleteExecution.DescentCodec.assignmentTerm,RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm,MatchAutomataBindingExecution.payloadBindingTerm,InferenceCettaWire.AuthoredRule.contextualValueTerm,InferenceCettaWire.encodeList]

private theorem grounding_cons (name : String) (names : List String) (assignment : ScopedRuleMatching.Assignment) :
    ClosureMachine.grounding? (name :: names) assignment = (do
      let value ← bindingResult (Join.logicalVariable name) assignment
      let rest ← ClosureMachine.grounding? names assignment
      pure ((name,value) :: rest)) := by
  simp only [ClosureMachine.grounding?,List.mapM_cons,bindingResult]
  cases found : ScopedRuleMatching.lookup assignment (Join.logicalVariable name) with
  | none => simp
  | some value =>
    by_cases ground : value.dependencies = [] ∧ value.ambient = 0 <;> simp [ground]

theorem grounding_returns (state : State) (names : List String) (assignment : ScopedRuleMatching.Assignment) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:grounding"
        [encoded (encodeList (fun name => .application "SnapshotVariable"
          [.string name,.string (Join.logicalVariable name)]) names),
         encoded (CompleteExecution.DescentCodec.assignmentTerm assignment)]) state
      (encoded (encodeOption (encodeList (fun (name,value) =>
        .application "Binding" [.string name,InferenceCettaWire.encodePattern value]))
        (ClosureMachine.grounding? names assignment))) := by
  induction names with
  | nil =>
    metta_call checked
    metta_eval with checked unfolding [ClosureMachine.grounding?]
  | cons name names ih =>
    have first := binding_returns state (Join.logicalVariable name) assignment
    cases found : bindingResult (Join.logicalVariable name) assignment with
    | none =>
      rw [found] at first
      simp only [grounding_cons,found]
      metta_call checked
      metta_eval [first] with checked
    | some value =>
      rw [found] at first
      cases tail : ClosureMachine.grounding? names assignment with
      | none =>
        rw [tail] at ih
        simp only [grounding_cons,found,tail]
        metta_call checked
        metta_eval [first,ih] with checked
      | some values =>
        rw [tail] at ih
        simp only [grounding_cons,found,tail]
        metta_call checked
        metta_eval [first,ih] with checked

#print axioms binding_returns
#print axioms grounding_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
