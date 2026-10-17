import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Steps

/-!
# How deep an equation's premises go

`gslt:equations:limit` is `EquationJob.premisesBound`: when the plan's rules and the equation's
premises descend, and the capture binds every variable of the left side, every premise derivation
fits in the left side's constant size plus the sizes of the captured values; otherwise there is no
bound. The MeTTa reads the equation's depth declaration by its position, then weighs the capture.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding PatternTreeSize
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit

@[metta_head "gslt:equations:lookup"]
theorem equations_lookup_returns (state : State) (name : String) : ∀ assignment : Assignment,
    PureReturns runtime [] state (apply "gslt:equations:lookup" [encoded (.string name), assignmentValue assignment])
      state (encoded (RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm (lookup assignment name)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [assignmentValue, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList, lookup,
      RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm, MatchAutomataBindingExecution.payloadOptionTerm]
  | (other, value) :: rest => by
    have later := equations_lookup_returns state name rest
    by_cases same : other = name
    · subst same
      metta_call complete_checked
      metta_eval unfolding [assignmentValue, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
        MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm, encodeList,
        lookup, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
        MatchAutomataBindingExecution.payloadOptionTerm]
    · rw [show lookup ((other, value) :: rest) name = lookup rest name by simp [lookup, same]]
      metta_call complete_checked
      metta_eval [later] with complete_checked
        unfolding [assignmentValue, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
          MatchAutomataBindingExecution.payloadBindingsTerm, MatchAutomataBindingExecution.payloadBindingTerm,
          encodeList, same]

/-- The total size of the captured values of the names, when each is captured. -/
def weightOf (assignment : Assignment) : List String → Option Nat
  | [] => some 0
  | name :: rest =>
      match lookup assignment name with
      | none => none
      | some value => (weightOf assignment rest).map (nodes value.body + ·)

theorem weightOf_eq (assignment : Assignment) : ∀ names : List String,
    weightOf assignment names =
      if names.all (fun name => (lookup assignment name).isSome) then
        some (names.map (GeneralEquationAdmission.capturedWeight assignment)).sum
      else none
  | [] => rfl
  | name :: rest => by
    rw [weightOf, weightOf_eq assignment rest]
    cases found : lookup assignment name with
    | none => simp [found]
    | some value =>
      by_cases captured : rest.all (fun name => (lookup assignment name).isSome) = true
      · simp [found, captured, GeneralEquationAdmission.capturedWeight]
      · simp [found, captured]

@[metta_head "gslt:equations:weight"]
theorem equations_weight_returns (state : State) (assignment : Assignment) : ∀ names : List String,
    PureReturns runtime [] state
      (apply "gslt:equations:weight" [encoded (encodeList Term.string names), assignmentValue assignment])
      state (encoded (encodeOption Term.natural (weightOf assignment names)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, weightOf]
  | name :: rest => by
    have found := equations_lookup_returns state name assignment
    have later := equations_weight_returns state assignment rest
    cases looked : lookup assignment name with
    | none =>
      metta_call complete_checked
      metta_eval [found] with complete_checked
        unfolding [encodeList, weightOf, looked, RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
          MatchAutomataBindingExecution.payloadOptionTerm]
    | some value =>
      have size := nodes_returns state value.body
      cases weighed : weightOf assignment rest with
      | none =>
        metta_call complete_checked
        metta_eval [found, later] with complete_checked
          unfolding [encodeList, weightOf, looked, weighed,
            RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
            MatchAutomataBindingExecution.payloadOptionTerm, InferenceCettaWire.AuthoredRule.contextualValueTerm]
      | some sum =>
        rw [show weightOf assignment (name :: rest) = some (nodes value.body + sum) by simp [weightOf, looked, weighed],
          show encoded (encodeOption Term.natural (some (nodes value.body + sum))) =
            .expression [.symbol "Some", number (nodes value.body + sum)] from rfl]
        metta_call complete_checked
        metta_eval [found, later, size] with complete_checked
          unfolding [encodeList, looked, weighed,
            RuleInstantiationExecution.ScopedCapture.contextualValueOptionTerm,
            MatchAutomataBindingExecution.payloadOptionTerm, InferenceCettaWire.AuthoredRule.contextualValueTerm,
            patternValue]
        all_goals
          refine PureData.constructor_return completeLibrary.runtime _ _ "Some" _ _ ?_ (by decide) ?_
          · decide +kernel
          · exact .cons (natural_add_returns _ _ _ _ _ _ _ (bound_returns _ _ _ (by rfl))
              (bound_returns _ _ _ (by rfl))) .nil

/-- The depth declaration of the first equation at a position. -/
def declaredDepthTerm (plan : GeneralExecutionAdmission.Plan) (position : Nat) :
    List (GeneralExecutionAdmission.EquationPlan × Nat) → Term
  | [] => .symbol "EquationUnbounded"
  | (equation, other) :: rest =>
      if other = position then CompletePlanWire.equationDepthTerm plan equation else declaredDepthTerm plan position rest

@[metta_head "gslt:equations:declared-depth"]
theorem equations_declared_depth_returns (state : State) (plan : GeneralExecutionAdmission.Plan) (position : Nat) :
    ∀ pairs : List (GeneralExecutionAdmission.EquationPlan × Nat),
      PureReturns runtime [] state
        (apply "gslt:equations:declared-depth"
          [number position, encoded (encodeList (CompletePlanWire.equationDeclarationTerm plan) pairs)])
        state (encoded (declaredDepthTerm plan position pairs))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, declaredDepthTerm]
  | (equation, other) :: rest => by
    have later := equations_declared_depth_returns state plan position rest
    by_cases same : other = position
    · subst same
      metta_call complete_checked
      metta_eval unfolding [encodeList, declaredDepthTerm, CompletePlanWire.equationDeclarationTerm]
    · metta_call complete_checked
      metta_eval [later] with complete_checked
        unfolding [encodeList, declaredDepthTerm, CompletePlanWire.equationDeclarationTerm, same]

theorem declaredDepthTerm_zipIdx (plan : GeneralExecutionAdmission.Plan) :
    ∀ (equations : List GeneralExecutionAdmission.EquationPlan) (start : Nat)
      (equation : GeneralExecutionAdmission.EquationPlan) (position : Nat),
      (equation, position) ∈ equations.zipIdx start →
        declaredDepthTerm plan position (equations.zipIdx start) = CompletePlanWire.equationDepthTerm plan equation
  | [], _, _, _, member => by simp at member
  | first :: rest, start, equation, position, member => by
    rw [List.zipIdx_cons] at member ⊢
    rcases List.mem_cons.mp member with here | later
    · cases here
      simp [declaredDepthTerm]
    · have bounded : start + 1 ≤ position := (List.mem_zipIdx later).1
      rw [declaredDepthTerm, if_neg (by omega)]
      exact declaredDepthTerm_zipIdx plan rest (start + 1) equation position later

/-- The premise limit of an equation at a capture. -/
def equationLimit (plan : GeneralExecutionAdmission.Plan) (equation : GeneralExecutionAdmission.EquationPlan)
    (captured : Assignment) : Option Nat :=
  if StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
      StructuralDescent.checkPremises equation.rule equation.binding.spec 0 equation.rule.premises then
    (weightOf captured equation.rule.left.freeFvarNames).map
      (GeneralEquationMeasures.constantContribution equation.rule.left + ·)
  else none

theorem equationLimit_eq (plan : GeneralExecutionAdmission.Plan) (job : GeneralEquationJobs.Job) (captured : Assignment) :
    equationLimit plan job.equation captured = Complete.EquationJob.premisesBound plan job captured := by
  unfold equationLimit Complete.EquationJob.premisesBound
  rw [weightOf_eq]
  by_cases checks : (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
      StructuralDescent.checkPremises job.equation.rule job.equation.binding.spec 0 job.equation.rule.premises) = true
  · by_cases captures : Complete.EquationDepth.capturesLeft job.equation.rule captured = true
    · have every : job.equation.rule.left.freeFvarNames.all (fun name => (lookup captured name).isSome) = true :=
        captures
      simp [checks, captures, every, Complete.EquationDepth.leftWeight]
    · have some : job.equation.rule.left.freeFvarNames.all (fun name => (lookup captured name).isSome) = false := by
        simpa [Complete.EquationDepth.capturesLeft] using captures
      simp [checks, captures, some]
  · simp at checks
    by_cases environment : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true
    · simp [environment, checks environment]
    · simp [environment]

@[metta_head "gslt:equations:limit"]
theorem equations_limit_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (table : List (String × TypeExpr)) (bound : List TypeExpr) (expected : TypeExpr)
    (equation : GeneralExecutionAdmission.EquationPlan) (position : Nat)
    (declared : (equation, position) ∈ plan.equations.zipIdx) (captured : Assignment) :
    PureReturns runtime [] state
      (apply "gslt:equations:limit" [planValue plan table bound expected, number position, assignmentValue captured])
      state (encoded (encodeOption Term.natural (equationLimit plan equation captured))) := by
  have depth := equations_declared_depth_returns state plan position plan.equations.zipIdx
  rw [declaredDepthTerm_zipIdx plan plan.equations 0 equation position declared] at depth
  unfold equationLimit
  by_cases checks : (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
      StructuralDescent.checkPremises equation.rule equation.binding.spec 0 equation.rule.premises) = true
  · have weighed := equations_weight_returns state captured equation.rule.left.freeFvarNames
    rw [if_pos checks]
    cases weight : weightOf captured equation.rule.left.freeFvarNames with
    | none =>
      complete_eval [depth, weighed]
        unfolding [planValue, CompletePlanWire.planTerm, CompletePlanWire.equationDepthTerm, checks, weight]
    | some sum =>
      rw [show encoded (encodeOption Term.natural (Option.map
          (GeneralEquationMeasures.constantContribution equation.rule.left + ·) (some sum))) =
        .expression [.symbol "Some", number (GeneralEquationMeasures.constantContribution equation.rule.left + sum)]
        from rfl]
      complete_eval [depth, weighed]
        unfolding [planValue, CompletePlanWire.planTerm, CompletePlanWire.equationDepthTerm, checks, weight]
      all_goals
        refine PureData.constructor_return completeLibrary.runtime _ _ "Some" _ _ ?_ (by decide) ?_
        · decide +kernel
        · exact .cons (natural_add_returns _ _ _ _ _ _ _ (bound_returns _ _ _ (by rfl))
            (bound_returns _ _ _ (by rfl))) .nil
  · have unchecked : (StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) &&
        StructuralDescent.checkPremises equation.rule equation.binding.spec 0 equation.rule.premises) = false := by
      simpa using checks
    rw [if_neg checks]
    complete_eval [depth] unfolding [planValue, CompletePlanWire.planTerm, CompletePlanWire.equationDepthTerm, unchecked]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
