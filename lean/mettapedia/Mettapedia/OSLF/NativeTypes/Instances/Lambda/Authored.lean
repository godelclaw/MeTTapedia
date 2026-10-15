import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier

open Mettapedia.OSLF.Framework

/-!
# Complete authored lambda premise readouts

Each congruence declaration consumes the actual ordered child list. The
comparison retains every child occurrence, including duplicate targets,
rather than requiring a singleton oracle answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.Authored

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison LambdaPatternRendering
open LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule lamCongRule localStep)

def lamSpec : RuleBindingSpec := lamCongRule.bindings.getD ⟨[], []⟩

def lamInitial {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) : Assignment :=
  [("B", { dependencies := [.base "Term"], ambient := Γ.length, body := encodeTerm body })]

def lamCompleted {Γ : Ctx sig} (body target : Term sig (.term :: Γ) .term) : Assignment :=
  [("C", { dependencies := [.base "Term"], ambient := Γ.length, body := encodeTerm target }),
   ("B", { dependencies := [.base "Term"], ambient := Γ.length, body := encodeTerm body })]

theorem lam_admitted : admittedFor lamCongRule lamSpec = true := by decide +kernel

def readFiring {Evidence : Type} (firing : RuleFiring Evidence) :
    List (PremiseEvent Evidence) × Pattern := (firing.history, firing.target)

theorem lam_readouts {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
    (children : List (Evidence × Term sig (.term :: Γ) .term))
    (answers : oracle (1 + Γ.length) (encodeTerm body) =
      children.map (fun child => (child.1, encodeTerm child.2))) :
    (applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      lamCongRule (encodeTerm (lamT body))).map readFiring =
      children.zipIdx.map (fun (child, ordinal) =>
        ([.step 0 ordinal child.1], encodeTerm (lamT child.2))) := by
  have bound : lamCongRule.bindings = some lamSpec := rfl
  have premises : lamCongRule.premises = [.scopedStep localStep] := rfl
  have localScoped : localStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, localStep, Pattern.isWellScopedAt]
  have bodyScope : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have checked := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at checked
    simpa only [Nat.add_comm] using checked
  have matched : matchRuleAt lamCongRule lamSpec Γ.length
      (encodeTerm (lamT body)) = [lamInitial body] :=
    LambdaAuthoredLamCongExecutionComparison.lam_match_recovers_intrinsic body
  have instantiated : instantiateAt? lamCongRule lamSpec Γ.length
      (.premise 0 0 0) [] 1 (lamInitial body) localStep.source = some (encodeTerm body) :=
    LambdaAuthoredLamCongExecutionComparison.premise_source_is_body body
  have captured (target : Term sig (.term :: Γ) .term) :
      matchAt lamCongRule lamSpec Γ.length (.premise 0 0 1) [] 1
        (lamInitial body) localStep.target (encodeTerm target) = [lamCompleted body target] :=
    LambdaAuthoredLamCongExecutionComparison.premise_target_recovers body target
  have reduced (target : Term sig (.term :: Γ) .term) :
      reduct? lamCongRule lamSpec Γ.length (lamCompleted body target) =
        some (encodeTerm (lamT target)) :=
    LambdaAuthoredLamCongExecutionComparison.reduct_is_lam body target
  have childScoped (target : Term sig (.term :: Γ) .term) :
      (encodeTerm target).isWellScopedAt (1 + Γ.length) = true := by
    have checked := encodeTerm_scoped target
    change (encodeTerm target).isWellScopedAt (Γ.length + 1) = true at checked
    simpa only [Nat.add_comm] using checked
  simp only [applyRuleWithOracle, bound, lam_admitted, if_true,
    matched,
    List.flatMap_singleton, premises, runPremises, premiseResults, localScoped,
    show localStep.binders.length = 1 from rfl,
    stepResults, instantiated,
    bodyScope, answers, List.zipIdx_map, List.flatMap_map]
  simp [captured, reduced, finish?, readFiring, encodeTerm_scoped, childScoped,
    ← List.map_eq_flatMap, List.filterMap_map, List.map_map, Function.comp_def]


def rootValue {Γ : Ctx sig} (term : Term sig Γ .term) : ContextualValue :=
  { dependencies := [], ambient := Γ.length, body := encodeTerm term }

def appInitial {Γ : Ctx sig} (function argument : Term sig Γ .term) : Assignment :=
  [("A", rootValue argument), ("F", rootValue function)]

def appCompletedL {Γ : Ctx sig} (function argument target : Term sig Γ .term) : Assignment :=
  ("G", rootValue target) :: appInitial function argument

theorem appL_readouts {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument : Term sig Γ .term)
    (children : List (Evidence × Term sig Γ .term))
    (answers : oracle Γ.length (encodeTerm function) =
      children.map (fun child => (child.1, encodeTerm child.2))) :
    (applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      appCongLRule (encodeTerm (appT function argument))).map readFiring =
      children.zipIdx.map (fun (child, ordinal) =>
        ([.step 0 ordinal child.1], encodeTerm (appT child.2 argument))) := by
  have bound : appCongLRule.bindings = some appCongLSpec := rfl
  have premises : appCongLRule.premises = [.scopedStep appCongLStep] := rfl
  have localScoped : appCongLStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, appCongLStep, Pattern.isWellScopedAt]
  have matched : matchRuleAt appCongLRule appCongLSpec Γ.length
      (encodeTerm (appT function argument)) = [appInitial function argument] :=
    LambdaAuthoredAppCongExecutionComparison.appL_match function argument
  have instantiated : instantiateAt? appCongLRule appCongLSpec Γ.length
      (.premise 0 0 0) [] 0 (appInitial function argument) appCongLStep.source =
        some (encodeTerm function) :=
    LambdaAuthoredAppCongExecutionComparison.appL_source function argument
  have captured (target : Term sig Γ .term) :
      matchAt appCongLRule appCongLSpec Γ.length (.premise 0 0 1) [] 0
        (appInitial function argument) appCongLStep.target (encodeTerm target) =
          [appCompletedL function argument target] :=
    LambdaAuthoredAppCongExecutionComparison.appL_target function argument target
  have reduced (target : Term sig Γ .term) :
      reduct? appCongLRule appCongLSpec Γ.length (appCompletedL function argument target) =
        some (encodeTerm (appT target argument)) :=
    LambdaAuthoredAppCongExecutionComparison.appL_reduct function argument target
  simp only [applyRuleWithOracle, bound, appCongL_binding_admitted, if_true,
    matched, List.flatMap_singleton, premises, runPremises, premiseResults, localScoped,
    show appCongLStep.binders.length = 0 from rfl,
    stepResults, instantiated, Nat.zero_add, encodeTerm_scoped, answers,
    List.zipIdx_map, List.flatMap_map]
  simp [captured, reduced, finish?, readFiring, encodeTerm_scoped,
    ← List.map_eq_flatMap, List.filterMap_map, List.map_map, Function.comp_def]

def appCompletedR {Γ : Ctx sig} (function argument target : Term sig Γ .term) : Assignment :=
  ("B", rootValue target) :: appInitial function argument

theorem appR_readouts {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument : Term sig Γ .term)
    (children : List (Evidence × Term sig Γ .term))
    (answers : oracle Γ.length (encodeTerm argument) =
      children.map (fun child => (child.1, encodeTerm child.2))) :
    (applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      appCongRRule (encodeTerm (appT function argument))).map readFiring =
      children.zipIdx.map (fun (child, ordinal) =>
        ([.step 0 ordinal child.1], encodeTerm (appT function child.2))) := by
  have bound : appCongRRule.bindings = some appCongRSpec := rfl
  have premises : appCongRRule.premises = [.scopedStep appCongRStep] := rfl
  have localScoped : appCongRStep.isWellScopedAt Γ.length = true := by
    simp [ScopedStepPremise.isWellScopedAt, appCongRStep, Pattern.isWellScopedAt]
  have matched : matchRuleAt appCongRRule appCongRSpec Γ.length
      (encodeTerm (appT function argument)) = [appInitial function argument] :=
    LambdaAuthoredAppCongExecutionComparison.appR_match function argument
  have instantiated : instantiateAt? appCongRRule appCongRSpec Γ.length
      (.premise 0 0 0) [] 0 (appInitial function argument) appCongRStep.source =
        some (encodeTerm argument) :=
    LambdaAuthoredAppCongExecutionComparison.appR_source function argument
  have captured (target : Term sig Γ .term) :
      matchAt appCongRRule appCongRSpec Γ.length (.premise 0 0 1) [] 0
        (appInitial function argument) appCongRStep.target (encodeTerm target) =
          [appCompletedR function argument target] :=
    LambdaAuthoredAppCongExecutionComparison.appR_target function argument target
  have reduced (target : Term sig Γ .term) :
      reduct? appCongRRule appCongRSpec Γ.length (appCompletedR function argument target) =
        some (encodeTerm (appT function target)) :=
    LambdaAuthoredAppCongExecutionComparison.appR_reduct function argument target
  simp only [applyRuleWithOracle, bound, appCongR_binding_admitted, if_true,
    matched, List.flatMap_singleton, premises, runPremises, premiseResults, localScoped,
    show appCongRStep.binders.length = 0 from rfl,
    stepResults, instantiated, Nat.zero_add, encodeTerm_scoped, answers,
    List.zipIdx_map, List.flatMap_map]
  simp [captured, reduced, finish?, readFiring, encodeTerm_scoped,
    ← List.map_eq_flatMap, List.filterMap_map, List.map_map, Function.comp_def]

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.Authored
