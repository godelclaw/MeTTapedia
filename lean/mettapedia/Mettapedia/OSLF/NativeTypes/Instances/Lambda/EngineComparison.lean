import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Authored
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Decode

open Mettapedia.OSLF.Framework

/-!+# The finite lambda frontier and the authored engine

The comparison is at ordered history-and-target readouts. Congruence premises
consume the complete child frontier, so their original declaration indices
and every child ordinal remain present.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.EngineComparison

open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison LambdaPatternRendering
open LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule lamCongRule)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier Mettapedia.OSLF.NativeTypes.Instances.Lambda.Authored

def readout {Γ : Ctx sig} (source : Term sig Γ .term) : List (RuleHistory × Pattern) :=
  (firings {} source).map fun entry => (entry.history, encodeTerm entry.target)

def children {Γ : Ctx sig} (source : Term sig Γ .term) :
    List (RuleHistory × Term sig Γ .term) :=
  (firings {} source).map fun entry => (entry.history, entry.target)

theorem children_render {Γ : Ctx sig} (source : Term sig Γ .term) :
    (children source).map (fun child => (child.1, encodeTerm child.2)) = readout source := by
  simp [children, readout, List.map_map, Function.comp_def]

def liftReadout (index : Nat) (entry : List (PremiseEvent RuleHistory) × Pattern) :
    RuleHistory × Pattern := (.fire index entry.1, entry.2)

theorem rewrite_split (fuel ambient : Nat) (source : Pattern) :
    rewriteAt RelationEnv.empty language (fuel + 1) ambient source =
      ((applyRuleWithOracle (rewriteAt RelationEnv.empty language fuel)
          RelationEnv.empty language ambient betaRule source).map readFiring).map (liftReadout 0) ++
      ((applyRuleWithOracle (rewriteAt RelationEnv.empty language fuel)
          RelationEnv.empty language ambient lamCongRule source).map readFiring).map (liftReadout 1) ++
      ((applyRuleWithOracle (rewriteAt RelationEnv.empty language fuel)
          RelationEnv.empty language ambient appCongLRule source).map readFiring).map (liftReadout 2) ++
      ((applyRuleWithOracle (rewriteAt RelationEnv.empty language fuel)
          RelationEnv.empty language ambient appCongRRule source).map readFiring).map (liftReadout 3) := by
  have rules : language.rewrites.zipIdx =
      [(betaRule, 0), (lamCongRule, 1), (appCongLRule, 2), (appCongRRule, 3)] := rfl
  simp [rewriteAt, rules, List.map_map, readFiring, liftReadout, List.append_assoc, Function.comp_def]

theorem beta_readouts {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (source : Term sig Γ .term) :
    (applyRuleWithOracle oracle RelationEnv.empty language Γ.length
      betaRule (encodeTerm source)).map readFiring =
      (betaFirings {} source).map (fun entry => ([], encodeTerm entry.target)) := by
  match source with
  | .var _ =>
      simp [applyRuleWithOracle, betaRule, matchRuleAt, matchRuleWithAt, matchAtWith,
        encodeTerm, betaFirings]
  | .op .lam (.cons _ .nil) =>
      simp [applyRuleWithOracle, betaRule, matchRuleAt, matchRuleWithAt, matchAtWith,
        encodeTerm, encodeArgs, betaFirings]; rfl
  | .op .app (.cons function (.cons argument .nil)) =>
      match function with
      | .var _ =>
          simp [applyRuleWithOracle, betaRule, matchRuleAt, matchRuleWithAt,
            matchAtWith, matchArgsAtWith, encodeTerm, encodeArgs, wrapBinders,
            betaFirings, betaAtApp]; rfl
      | .op .app (.cons _ (.cons _ .nil)) =>
          simp [applyRuleWithOracle, betaRule, matchRuleAt,
            matchRuleWithAt, matchAtWith, matchArgsAtWith,
            encodeTerm, encodeArgs, wrapBinders, betaFirings, betaAtApp]; rfl
      | .op .lam (.cons body .nil) =>
          have actual := LambdaAuthoredBetaExecutionComparison.authored_beta_executes_intrinsic
            oracle body argument
          change applyRuleWithOracle oracle RelationEnv.empty language Γ.length
            betaRule (encodeTerm (appT (lamT body) argument)) = _ at actual
          erw [actual]
          rfl

theorem lam_rejects_app {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (function argument : Term sig Γ .term) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length lamCongRule
      (encodeTerm (appT function argument)) = [] := by
  simp [applyRuleWithOracle, lamCongRule, matchRuleAt, matchRuleWithAt,
    matchAtWith, appT, encodeTerm, encodeArgs]

theorem appL_rejects_lam {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length appCongLRule
      (encodeTerm (lamT body)) = [] := by
  simp [applyRuleWithOracle, appCongLRule, matchRuleAt, matchRuleWithAt,
    matchAtWith, lamT, encodeTerm, encodeArgs]

theorem appR_rejects_lam {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length appCongRRule
      (encodeTerm (lamT body)) = [] := by
  simp [applyRuleWithOracle, appCongRRule, matchRuleAt, matchRuleWithAt,
    matchAtWith, lamT, encodeTerm, encodeArgs]

theorem nodeCount_positive {Γ : Ctx sig} (source : Term sig Γ .term) :
    0 < nodeCount source := by
  cases source with
  | var => exact Nat.zero_lt_one
  | op => simp only [nodeCount]; omega

/-- Every sufficiently deep actual authored run has exactly the finite
intrinsic frontier's ordered histories and targets, at every ambient context. -/
theorem engine_readout : {Γ : Ctx sig} → (source : Term sig Γ .term) →
    (fuel : Nat) → nodeCount source ≤ fuel →
    rewriteAt RelationEnv.empty language fuel Γ.length (encodeTerm source) = readout source
  | _, source, 0, enough => by
      have positive := nodeCount_positive source
      omega
  | _, .var value, fuel + 1, _ => by
      rw [rewrite_split]
      simp [applyRuleWithOracle, betaRule, lamCongRule, appCongLRule, appCongRRule,
        matchRuleAt, matchRuleWithAt, matchAtWith, encodeTerm, readout, firings]
  | Γ, .op .lam (.cons body .nil), fuel + 1, enough => by
      have childEnough : nodeCount body ≤ fuel := by
        simp only [nodeCount, argumentNodeCount] at enough
        omega
      have answer : rewriteAt RelationEnv.empty language fuel (1 + Γ.length) (encodeTerm body) =
          (children body).map (fun child => (child.1, encodeTerm child.2)) := by
        rw [children_render]
        have child := engine_readout body fuel childEnough
        change rewriteAt RelationEnv.empty language fuel (Γ.length + 1) (encodeTerm body) = _ at child
        simpa only [Nat.add_comm] using child
      erw [rewrite_split, beta_readouts,
        lam_readouts _ body (children body) answer,
        appL_rejects_lam, appR_rejects_lam]
      simp [readout, lamT, firings, betaFirings, children, List.zipIdx_map,
        List.map_map, liftReadout, liftLam, Function.comp_def]
      rfl
  | Γ, .op .app (.cons function (.cons argument .nil)), fuel + 1, enough => by
      have functionEnough : nodeCount function ≤ fuel := by
        simp only [nodeCount, argumentNodeCount] at enough
        omega
      have argumentEnough : nodeCount argument ≤ fuel := by
        simp only [nodeCount, argumentNodeCount] at enough
        omega
      have functionAnswer : rewriteAt RelationEnv.empty language fuel Γ.length (encodeTerm function) =
          (children function).map (fun child => (child.1, encodeTerm child.2)) := by
        rw [children_render]
        exact engine_readout function fuel functionEnough
      have argumentAnswer : rewriteAt RelationEnv.empty language fuel Γ.length (encodeTerm argument) =
          (children argument).map (fun child => (child.1, encodeTerm child.2)) := by
        rw [children_render]
        exact engine_readout argument fuel argumentEnough
      erw [rewrite_split, beta_readouts, lam_rejects_app,
        appL_readouts _ function argument (children function) functionAnswer,
        appR_readouts _ function argument (children argument) argumentAnswer]
      simp [readout, appT, firings, children, List.zipIdx_map,
        List.map_map, liftReadout, liftAppL, liftAppR, Function.comp_def,
        List.append_assoc]
      erw [List.map_append, List.map_append]
      simp only [List.map_map, Function.comp_def, List.append_assoc]
      congr 1
      match function with
      | .var _ => rfl
      | .op .app (.cons _ (.cons _ .nil)) => rfl
      | .op .lam (.cons _ .nil) => rfl
termination_by _ source _ _ => nodeCount source
decreasing_by all_goals simp only [nodeCount, argumentNodeCount]; omega

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.EngineComparison
